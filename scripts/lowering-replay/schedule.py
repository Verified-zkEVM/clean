"""Find a configure order whose real registration reproduces Lean's query lists.

Usage: schedule.py REPLAY.json SCHEDULE.json. Events are gates (each closure queries its recorded
call order, then `query_cells` walks the folded polynomials), additive gates (closure order, then
the atoms as built), lookups (closure order, bare tables unless `batched_lookup_any`, then the
walk), enable_equality per permutation column and enable_constant per
constants column. Within a kind the order is Lean's; the interleaving is searched, and so is each
lookup's closure among its value-equal records (`candidates`; twins are indistinguishable after a
hand edit), the choice written back to REPLAY.json. With no such
order the schedule is `forced`: the harness then registers Lean's lists in the first closure and the
report says no Rust configure with these closures produces them."""
import json, sys

def atoms(e, out):
    tag = e[0]
    if tag in ("advice", "fixed", "instance"):
        out.append((tag, e[1], e[2]))
    elif tag in ("neg", "scaled", "scale"):
        atoms(e[1], out)
    elif tag in ("sum", "prod", "add", "sub", "mul"):
        atoms(e[1], out); atoms(e[2], out)
    return out

ZERO, ONE = ["const", "0"], ["const", "1"]

def fold(e):
    """The tree Rust's operators build from an erased tree or a spelling (circuit.rs:1180-1290)."""
    tag = e[0]
    if tag == "neg": return ["neg", fold(e[1])]
    if tag in ("scaled", "scale"): return ["scaled", fold(e[1]), e[2]]
    if tag in ("sum", "add"):
        a, b = fold(e[1]), fold(e[2])
        return b if a == ZERO else a if b == ZERO else ["sum", a, b]
    if tag == "sub":
        a, b = fold(e[1]), fold(e[2])
        return ["neg", b] if a == ZERO else a if b == ZERO else ["sum", a, ["neg", b]]
    if tag in ("prod", "mul"):
        a, b = fold(e[1]), fold(e[2])
        return ZERO if ZERO in (a, b) else b if a == ONE else a if b == ONE else ["prod", a, b]
    return e

def walk(e):
    """The atoms `query_cells` visits: those of the folded tree."""
    return atoms(fold(e), [])

def gate_queries(g, walked, target):
    """The closure's recorded call order; then `create_gate` walks `q * poly` (or the raw poly),
    while a trash body is queried as it is built, but for atoms Lean never registers, which are
    index-free `query_cell`s in a factor Rust folds away."""
    qs = [tuple(q) for q in g["queries"] if q[0] != "sel"]
    for c in g["constraints"]:
        if not walked: qs += [a for a in atoms(c["poly"], []) if (a[1], a[2]) in target[a[0]]]
        elif g.get("raw") or fold(c["poly"]) != ZERO: qs += walk(c["poly"])
    return qs

def lookup_queries(l):
    """The closure's recorded call order, then Rust queries bare table columns, then
    `batched_lookup_any` walks each column's inputs and table."""
    bare = not l.get("any") and all(t[0] == "fixed" and t[2] == 0 for t in l["table"])
    own = [tuple(q) for q in l.get("queries", []) if q[0] != "sel"]
    if bare: own += [tuple(t) for t in l["table"]]
    for w, t in enumerate(l["table"]):
        for row in l["inputs"]: own += walk(row[w])
        own += walk(t)
    return own

def main(src, dst):
    replay = json.load(open(src)); cs = replay["cs"]
    records = cs.get("lookup_closures", [])
    def closures(i):
        l = cs["lookups"][i]
        return [(j, {**l, **records[j]}) for j in l.get("candidates", [])] + [(None, l)]
    target = {k: [tuple(x) for x in cs[f"{k}_queries"]] for k in ("advice", "fixed", "instance")}
    perm_t, const_t = [tuple(c) for c in cs["permutation"]], cs["constants"]
    kinds = {"equality": len(perm_t), "constant": len(const_t), "gate": len(cs["gates"]),
             "trash": len(cs["trashcans"]), "lookup": len(cs["lookups"])}
    def effect(kind, i):
        if kind == "gate": return gate_queries(cs["gates"][i], True, target), []
        if kind == "trash": return gate_queries(cs["trashcans"][i], False, target), []
        if kind == "equality": c = perm_t[i]; return [(c[0], c[1], 0)], [c]
        return None, None

    def apply(state, kind, i, choice=None):
        q, perm, consts, used = state
        q = {k: list(v) for k, v in q.items()}; perm = list(perm); consts = list(consts)
        if kind == "lookup":
            j, l = choice
            if j is not None and j in used: return None
            used = used | ({j} if j is not None else set())
            new_q, new_p = lookup_queries(l), []
        elif kind == "constant":
            c = const_t[i]
            if c in consts: return (q, perm, consts, used)
            consts.append(c); new_q, new_p = [("fixed", c, 0)], [("fixed", c)]
        else:
            new_q, new_p = effect(kind, i)
        for kq, col, r in new_q:
            if (col, r) not in q[kq]: q[kq].append((col, r))
        for c in new_p:
            if c not in perm: perm.append(c)
        ok = all(q[k] == target[k][:len(q[k])] for k in q) and perm == perm_t[:len(perm)] and consts == const_t[:len(consts)]
        return (q, perm, consts, used) if ok else None

    order = list(kinds)
    failed = set()
    sys.setrecursionlimit(100000)
    def search(idx, state, events):
        if all(idx[k] == kinds[k] for k in order):
            q, perm, consts, _ = state
            return events if all(q[k] == target[k] for k in q) and perm == perm_t and consts == const_t else None
        # The closure choices make the state more than the counts.
        key = (tuple(idx[k] for k in order), tuple(tuple(v) for v in state[0].values()),
               tuple(state[1]), tuple(state[2]), state[3])
        if key in failed: return None
        for k in order:
            if idx[k] < kinds[k]:
                for choice in (closures(idx[k]) if k == "lookup" else [None]):
                    nxt = apply(state, k, idx[k], choice)
                    if nxt is not None:
                        event = [k, idx[k]] + ([choice[0]] if k == "lookup" else [])
                        found = search({**idx, k: idx[k] + 1}, nxt, events + [event])
                        if found is not None: return found
        failed.add(key)
        return None
    events = search({k: 0 for k in order}, ({k: [] for k in target}, [], [], frozenset()), [])
    forced = events is None
    if forced:
        events = [[k, i] for k in ("gate", "trash", "lookup", "equality", "constant") for i in range(kinds[k])]
    else:
        for e in events:
            if e[0] == "lookup" and e[2] is not None:
                cs["lookups"][e[1]].update(records[e[2]])
        json.dump(replay, open(src, "w"))
    json.dump({"forced": forced, "events": events}, open(dst, "w"))
    print(f"schedule: {'FORCED (no registering order)' if forced else 'found'}, {len(events)} events")

if __name__ == "__main__":
    main(*sys.argv[1:3])

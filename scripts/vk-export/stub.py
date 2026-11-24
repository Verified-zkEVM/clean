"""Replace the proofs of top-level theorems, lemmas and examples by `sorry`, in place.

Usage: stub.py FILE.lean... The runner's fallback when a submission's proofs do not
elaborate against this formalization: `candidate` cannot depend on a proof's value.
Textual: a declaration runs from its column-0 keyword to the next column-0 line, and its
proof starts at the first `:=`, `where` or `|` outside brackets, comments and strings."""
import re, sys
from pathlib import Path

DECL = re.compile(r"(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|nonrec)\s+)*(theorem|lemma|example)\b")
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"

def proof_start(text, start):
    depth, i = 0, start
    while i < len(text):
        if text.startswith("--", i): i = text.find("\n", i); i = len(text) if i < 0 else i; continue
        if text.startswith("/-", i):
            nest, i = 1, i + 2
            while i < len(text) and nest:
                nest += text.startswith("/-", i) - text.startswith("-/", i)
                i += 2 if text.startswith(("/-", "-/"), i) else 1
            continue
        if text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"': i += 2 if text[i] == "\\" else 1
        elif text[i] in OPEN: depth += 1
        elif text[i] in CLOSE: depth -= 1
        elif depth == 0 and (text.startswith(":=", i) or text[i] == "|" and text[i - 1] in " \n"
                             or re.match(r"(?<![\w.])where\b", text[i:i + 6]) and not text[i - 1].isalnum()):
            return i
        i += 1
    return None

def stub(text):
    lines = text.split("\n")
    starts = [i for i, l in enumerate(lines) if l and not l[0].isspace() and not l.startswith(("--", ")"))]
    out, i = [], 0
    while i < len(lines):
        if i in starts and DECL.match(lines[i]):
            end = next((j for j in starts if j > i), len(lines))
            body = "\n".join(lines[i:end])
            at = proof_start(body, DECL.match(body).end())
            if at is not None:
                out.append(body[:at].rstrip() + " := sorry")
                out.extend(l for l in lines[i:end] if not l.strip())  # keep spacing
                i = end
                continue
        out.append(lines[i]); i += 1
    return "\n".join(out)

if __name__ == "__main__":
    for name in sys.argv[1:]:
        path = Path(name); path.write_text(stub(path.read_text()))

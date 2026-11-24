// Prints the non-ASCII ranges `<str as Debug>` escapes (Midnight/Keygen/DebugEscape.lean), checking the
// escape is `\u{hex}` and does not depend on position. Run with midnight-zk's toolchain: rustc -O debug-escape.rs.
fn escaped(c: char, prefix: &str) -> bool {
    let s = format!("{prefix}{c}");
    let d = format!("{:?}", s);
    let plain = format!("\"{s}\"");
    if d == plain { return false; }
    let want = format!("\"{prefix}\\u{{{:x}}}\"", c as u32);
    assert_eq!(d, want, "unexpected escape for {:x}", c as u32);
    true
}
fn ranges(prefix: &str) -> Vec<(u32, u32)> {
    let mut out: Vec<(u32, u32)> = vec![];
    for n in 0x80u32..=0x10FFFF {
        let Some(c) = char::from_u32(n) else { continue };
        if escaped(c, prefix) {
            match out.last_mut() { Some(r) if r.1 + 1 == n => r.1 = n, _ => out.push((n, n)) }
        }
    }
    out
}
fn main() {
    let a = ranges(""); let b = ranges("a");
    println!("same={} count={}", a == b, a.len());
    let body: Vec<String> = a.iter().map(|(l, h)| format!("(0x{l:x}, 0x{h:x})")).collect();
    std::fs::write("ranges.txt", body.join(", ")).unwrap();
}

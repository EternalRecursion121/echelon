#!/usr/bin/env python3
"""Export every level tagged `-- @sheet N Qk` as a tutorial answer pack.

Usage: python3 scripts/export_sheet.py N [--out exports/] [--progress my-progress.json]
                                           [--hand-in] [--pdf] [--name "Your Name"]

With --progress (the JSON from the game's "Download progress" button, which works on the
public server), each question shows YOUR proof from the game instead of the sample proof,
marks unsolved questions, and notes on how many proof rows you opened hidden hints.

--hand-in (needs --progress) produces what you submit: each question (the sheet's wording
only, not the game's instructions), your explanation (every `-- Explain:` comment block in
your proof, printed as plain text), your Lean proof and the hint count — and no model
answers. --pdf also renders the Markdown to PDF (pandoc + lualatex).

For each tagged level it emits, informal-first: the question (level Introduction), the
tutorial answer (a `/-! @answer ... -/` block in the level file, falling back to the
Conclusion), then the Lean certificate — the statement and sample proof with game-only
lines (Hint/Branch) stripped. Levels are ordered by question number.
"""
import json, re, subprocess, sys, pathlib, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
TAG = re.compile(r"^--\s*@sheet\s+(\d+)\s+Q(\S+)", re.M)
LEAN_STRING = r'"((?:[^"\\]|\\.)*)"'


def lean_unescape(s):
    """Undo Lean string escapes: \\\\ -> \\, \\" -> ", \\n -> newline, \\t -> tab."""
    return re.sub(r"\\(.)", lambda m: {"n": "\n", "t": "\t"}.get(m.group(1), m.group(1)), s, flags=re.S)


def string_block(src, keyword):
    m = re.search(keyword + r"\s+" + LEAN_STRING, src, re.S)
    return lean_unescape(m.group(1)).strip() if m else ""


LIST_ITEM = re.compile(r"\s*([*-]|\d+\.)\s")


def fix_lists(text):
    """Pandoc needs a blank line before a list that follows a paragraph line (the game's
    Markdown renderer does not); insert one so the PDF shows a list, not one run-on line."""
    lines, out, in_math = text.split("\n"), [], False
    for i, line in enumerate(lines):
        if i and not in_math and LIST_ITEM.match(line) and lines[i - 1].strip() \
                and not LIST_ITEM.match(lines[i - 1]) and not lines[i - 1].startswith("  "):
            out.append("")
        out.append(line)
        in_math ^= line.count("$$") % 2 == 1
    return "\n".join(out)


def sheet_text(intro):
    """Only the sheet's wording: the `**Problem Sheet …**` paragraph, the paragraphs of the
    question's parts that follow it ((a), (b), … / the sheet's own hint), and any
    `*Formulation.*` note saying how the Lean statement reformulates the question."""
    paras = [p.strip() for p in re.split(r"\n\s*\n", intro) if p.strip()]
    start = next((i for i, p in enumerate(paras) if p.startswith("**Problem Sheet")), None)
    if start is None:
        return intro
    keep = [paras[start]]
    i = start + 1
    while i < len(paras) and re.match(r"(\*\*)?\([a-z]\)|\*Hint \(from the sheet\)", paras[i]):
        keep.append(paras[i])
        i += 1
    keep += [p for p in paras[i:] if p.startswith("*Formulation.*")]
    return "\n\n".join(keep)


def _string_end(text, pos):
    """Index just after the Lean string literal starting at text[pos] == '"' (or len)."""
    i = pos + 1
    while i < len(text):
        if text[i] == "\\":
            i += 2
            continue
        if text[i] == '"':
            return i + 1
        i += 1
    return len(text)


def strip_game_lines(body):
    """Remove Hint/Branch commands (also `· Hint …` after a bullet, and multi-line hint
    strings) so that what remains is the plain Lean proof."""
    out = []
    skip_branch = None       # indent of a Branch whose (deeper) body we are dropping
    bullet = None            # indent of a `·` whose first tactic was a Hint
    pos = 0                  # walk the flat string so multi-line hint strings are skipped exactly
    while pos < len(body):
        nl = body.find("\n", pos)
        line = body[pos:] if nl == -1 else body[pos:nl]
        nxt = len(body) if nl == -1 else nl + 1
        indent = len(line) - len(line.lstrip())
        stripped = line.strip()
        if skip_branch is not None:
            if stripped and indent > skip_branch:
                pos = nxt
                continue
            skip_branch = None
        m = re.match(r"(\s*)(·\s*)?(Hint|Branch)\b", line)
        if m:
            if m.group(2):
                bullet = indent if bullet is None else bullet
            if m.group(3) == "Branch":
                skip_branch = indent
                pos = nxt
                continue
            q = body.find('"', pos)
            if q != -1:
                end = _string_end(body, q)
                nl2 = body.find("\n", end)
                pos = len(body) if nl2 == -1 else nl2 + 1
            else:
                pos = nxt
            continue
        if bullet is not None and stripped:
            if indent > bullet:
                out.append(" " * bullet + "· " + stripped)
            else:
                out.append(" " * bullet + "·")
                out.append(line)
            bullet = None
        else:
            out.append(line)
        pos = nxt
    if bullet is not None:
        out.append(" " * bullet + "·")
    return "\n".join(out)


def proof_block(src):
    m = re.search(r"(/--.*?-/\s*)?(Statement.*?:= by\n)(.*?)(?=\n(?:end |Conclusion|/--|\S))", src, re.S)
    if not m:
        return "", ""
    doc = (m.group(1) or "").strip().removeprefix("/--").removesuffix("-/").strip()
    return doc, strip_game_lines(m.group(2) + m.group(3)).rstrip()


def answer_block(src):
    m = re.search(r"/-!\s*@answer\s*(.*?)-/", src, re.S)
    return m.group(1).strip() if m else ""


def world_level(src):
    w = re.search(r'^World\s+"([^"]+)"', src, re.M)
    l = re.search(r"^Level\s+(\d+)", src, re.M)
    return (w.group(1), l.group(1)) if w and l else (None, None)


def player_proof(progress, world, level):
    """(code, completed, hints_opened) from a downloaded GameProgress JSON, or None."""
    lv = progress.get("data", {}).get(world, {}).get(str(level))
    if not lv:
        return None
    return (lv.get("code") or "").strip(), lv.get("completed", False), len(lv.get("help", []))


def qkey(q):
    m = re.match(r"(\d+)(.*)", q)
    return (int(m.group(1)), m.group(2)) if m else (999, q)


def explanations(proof):
    """Every `-- Explain:` comment block in the player's proof, in order, each joined into
    one paragraph (a block continues over the following `--` comment lines)."""
    blocks, cur = [], None
    for line in proof.splitlines():
        t = line.strip()
        if t.startswith("-- Explain:"):
            if cur is not None:
                blocks.append(cur)
            cur = [t[len("-- Explain:"):].strip()]
        elif cur is not None and t.startswith("--"):
            cur.append(t[2:].strip())
        elif cur is not None:
            blocks.append(cur)
            cur = None
    if cur is not None:
        blocks.append(cur)
    return [" ".join(l for l in b if l) for b in blocks if any(b)]


MD_SPECIAL = re.compile(r"([\\`*_{}\[\]()#+\-.!<>|~^$&@:'\"=])")
INLINE_MATH = re.compile(r"\$(?=\S)([^$]*?\S)\$(?!\d)")


def plain(text):
    """Escape every Markdown/TeX-active character so the text prints literally."""
    return MD_SPECIAL.sub(r"\\\1", text)


def safe_text(text, math=True):
    """Player text as Markdown that cannot reformat or break the document. With math=True,
    `$…$` spans are kept as LaTeX math (everything else is escaped); math=False escapes all."""
    if not math:
        return plain(text)
    out, last = [], 0
    for m in INLINE_MATH.finditer(text):
        out.append(plain(text[last:m.start()]))
        out.append(m.group(0))
        last = m.end()
    out.append(plain(text[last:]))
    return "".join(out)


def explanation_md(blocks, math=True):
    if not blocks:
        return []
    md = ["**Explanation.**", ""]
    for i, b in enumerate(blocks):
        if i:
            md.append(">")
        md.append("> " + safe_text(b, math))
    return md + [""]


# Questions the sheet does NOT split into lettered parts, although the game tags them Q7a, Q7b, …
# (one level per step; the letters keep coverage checks working). Printed as "(part i of n)".
# Keep in sync with scripts/sheet_index.py.
UNLETTERED = {8: {"6"}, 9: {"7", "8"}, 10: {"2", "6"}}


def heading_key(sheet, q):
    """The printed question for a tag: '7a' -> '7' when the sheet's Question 7 has no parts."""
    m = re.match(r"(\d+)", q)
    return m.group(1) if m and m.group(1) in UNLETTERED.get(sheet, ()) else q


def headings(entries, sheet=0):
    """'Question 3a' etc.; a tag shared by several levels (or several game parts of an
    unlettered sheet question) gets '(part i of n)'."""
    keys = [heading_key(sheet, e[0]) for e in entries]
    counts = {}
    for k in keys:
        counts[k] = counts.get(k, 0) + 1
    seen, out = {}, []
    for k in keys:
        q = k.replace("-", "–")
        if counts[k] > 1:
            seen[k] = seen.get(k, 0) + 1
            out.append(f"Question {q} (part {seen[k]} of {counts[k]})")
        else:
            out.append(f"Question {q}")
    return out


PANDOC_ARGS = ["--pdf-engine=lualatex", "-V", "geometry:margin=2.2cm",
               "-V", "mainfont=STIX Two Text", "-V", "mathfont=STIX Two Math"]


def pandoc(md_text, pdf):
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as fh:
        fh.write(md_text)
    r = subprocess.run(["pandoc", fh.name, "-o", str(pdf), *PANDOC_ARGS,
                        "-H", str(ROOT / "scripts" / "pdf-header.tex")], capture_output=True, text=True)
    pathlib.Path(fh.name).unlink()
    return r


def collect(sheet, progress):
    entries = []
    for f in sorted((ROOT / "Game" / "Levels").rglob("*.lean")):
        src = f.read_text()
        for m in TAG.finditer(src):
            if int(m.group(1)) != sheet:
                continue
            doc, proof = proof_block(src)
            note = ""
            if progress is not None:
                mine = player_proof(progress, *world_level(src))
                if mine and mine[0]:
                    code, done, hints = mine
                    # the hand-in shows `Statement : …`, not the game's internal statement name
                    header = re.sub(r"^Statement\s+[\w.]+(?=[\s:({\[])", "Statement",
                                    proof.split(":= by")[0]) + ":= by"
                    proof = header + "\n" + "\n".join("  " + l for l in code.splitlines())
                    note = ("✓ solved in the game" if done else "✗ not yet solved in the game") + \
                           (f" · hidden hints opened on {hints} proof row(s)" if hints else " · no hidden hints opened")
                else:
                    proof, note = "-- not attempted yet", "✗ not attempted in the game"
            entries.append((m.group(2), f.relative_to(ROOT), fix_lists(string_block(src, "Introduction")),
                            doc, proof, fix_lists(answer_block(src) or string_block(src, "Conclusion")), note))
    entries.sort(key=lambda e: qkey(e[0]))
    return entries


def render(sheet, entries, hand_in, progress, name, math_ok):
    """Markdown lines. math_ok: set of indices whose explanation may keep $…$ math."""
    heads = headings(entries, sheet)
    if hand_in:
        md = [f"# Linear Algebra MT2026 — Problem Sheet {sheet}" + (f" — {plain(name)}" if name else ""), "",
              "Proofs written and checked in Lean 4 (Mathlib) in the *Echelon* game.", ""]
        for k, (q, path, intro, doc, proof, concl, note) in enumerate(entries):
            md += [f"## {heads[k]}", "", sheet_text(intro), "", f"*{note}*", ""]
            md += explanation_md(explanations(proof), k in math_ok)
            md += [f"*Claim.* {doc}" if doc else "", "", "```lean", proof, "```", ""]
    else:
        md = [f"# Problem Sheet {sheet} — worked answers (Lean-checked)\n"]
        for k, (q, path, intro, doc, proof, concl, note) in enumerate(entries):
            md += [f"## {heads[k]}\n", intro, "",
                   ("### Model answer (check yours against it)\n" if progress is not None else "### Answer\n"),
                   concl, ""]
            if progress is not None:
                md += explanation_md(explanations(proof), k in math_ok)
            md += ["### Lean certificate" + (" (my proof)" if progress is not None else "") + "\n",
                   f"*{note}*" if note else "", f"*Claim.* {doc}" if doc else "",
                   "", "```lean", proof, "```", "", f"<sub>source: `{path}`</sub>", ""]
    return "\n".join(md)


def main():
    sheet = int(sys.argv[1])
    out = ROOT / (sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else "exports")
    progress = None
    if "--progress" in sys.argv:
        progress = json.loads(pathlib.Path(sys.argv[sys.argv.index("--progress") + 1]).read_text())
    hand_in = "--hand-in" in sys.argv
    if hand_in and progress is None:
        sys.exit("--hand-in needs --progress <file> (download it from the game's menu)")
    name = sys.argv[sys.argv.index("--name") + 1] if "--name" in sys.argv else ""
    entries = collect(sheet, progress)
    math_ok = set(range(len(entries)))
    out.mkdir(parents=True, exist_ok=True)
    stem = f"sheet{sheet}" + ("-hand-in" if hand_in else "")
    target = out / f"{stem}.md"
    md = render(sheet, entries, hand_in, progress, name, math_ok)
    target.write_text(md)
    print(f"wrote {target} ({len(entries)} questions)")
    if "--pdf" not in sys.argv:
        return
    pdf = out / f"{stem}.pdf"
    r = pandoc(md, pdf)
    if r.returncode != 0 and progress is not None:
        # Find the question(s) whose explanation math breaks LaTeX; print those as plain text.
        bad = []
        for k in range(len(entries)):
            if not explanations(entries[k][4]):
                continue
            one = render(sheet, [entries[k]], hand_in, progress, name, {0})
            if pandoc(one, out / f".{stem}-check.pdf").returncode != 0:
                bad.append(k)
        (out / f".{stem}-check.pdf").unlink(missing_ok=True)
        if bad:
            heads = headings(entries, sheet)
            for k in bad:
                print(f"warning: the $…$ maths in your explanation for {heads[k]} does not compile "
                      f"in LaTeX; it is printed as plain text instead.", file=sys.stderr)
            md = render(sheet, entries, hand_in, progress, name, math_ok - set(bad))
            target.write_text(md)
            r = pandoc(md, pdf)
    if r.returncode != 0:
        err = "\n".join(l for l in (r.stderr or "").splitlines() if l.strip())[-1500:]
        sys.exit(f"PDF rendering failed (pandoc exit {r.returncode}); the Markdown is in {target}.\n{err}")
    for line in (r.stderr or "").splitlines():
        if "Missing character" in line:
            print("warning: " + line.strip(), file=sys.stderr)
    print(f"wrote {pdf}")


if __name__ == "__main__":
    main()

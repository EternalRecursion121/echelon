#!/bin/bash
# Regression test for scripts/export_sheet.py + scripts/pdf-header.tex.
# Usage: scripts/test_export.sh [scratch dir]   (needs pandoc, lualatex, pdftotext; exit 0 = pass)
# Builds a fake progress file for Sheets 2 and 8 covering: a solved proof, an unsolved one, a
# `sorry`, two `-- Explain:` blocks, explanation text with `\cmd`, `2*x + 3*y`, `<b>`, `$…$`
# maths (valid and broken), a 200-character line, `→ₗ[ℝ]`, the ✗ mark and repeated/multi-part
# tags; then checks the Markdown and the rendered PDF text.
set -u
cd "$(dirname "$0")/.."
DIR=${1:-${TMPDIR:-/tmp}}/test_export
rm -rf "$DIR"; mkdir -p "$DIR"
exec python3 -I - "$DIR" <<'PY'
import json, pathlib, re, subprocess, sys
DIR = pathlib.Path(sys.argv[1])
ROOT = pathlib.Path.cwd()
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / "scripts"))
import export_sheet as E

fails = []
def check(ok, what):
    print(("ok   " if ok else "FAIL ") + what)
    if not ok:
        fails.append(what)

def level_of(sheet, q):
    for f in sorted((ROOT / "Game/Levels").rglob("L*.lean")):
        s = f.read_text()
        if re.search(rf"^--\s*@sheet\s+{sheet}\s+Q{re.escape(q)}\s*$", s, re.M):
            return E.world_level(s)
    raise SystemExit(f"no level tagged S{sheet} Q{q}")

LONG = "-- " + " ".join(["word"] * 45) + " ENDOFLONGLINE"          # > 200 characters
assert len(LONG) > 200
two_blocks = "\n".join([
    "-- Explain: First block. If 2*x + 3*y = 0 then <b>bold?</b> and \\cmd stay literal;",
    "-- maths stays maths: $x_1 + x_2 = \\lambda$ and a price of $5.",
    "intro h",
    "-- Explain: Second block about f : V →ₗ[ℝ] W, with _under_ and # hash.",
    LONG,
    "exact h"])
broken = "-- Explain: Broken maths $\\undefinedcontrolsequence x$ here.\nsorry"

w, l = level_of(2, "5")            # explain level, solved
w2, l2 = level_of(8, "1a")          # sorry, not solved
w3, l3 = level_of(2, "9a")          # solved, no explanation
progress = {"data": {}}
def put(w, l, code, done, help_):
    progress["data"].setdefault(w, {})[str(l)] = {"code": code, "completed": done, "help": help_}
put(w, l, two_blocks, True, [3, 5])
put(w3, l3, "exact foo  -- f : V →ₗ[ℝ] W", True, [])
put(w2, l2, broken, False, [1])
pf = DIR / "progress.json"
pf.write_text(json.dumps(progress))

# 1. Model packs: no game-only lines, no Lean string escapes, unique headings.
for n in range(1, 11):
    subprocess.run(["python3", "-I", "scripts/export_sheet.py", str(n), "--out", str(DIR)],
                   check=True, capture_output=True)
    md = (DIR / f"sheet{n}.md").read_text()
    code = "\n".join(re.findall(r"```lean\n(.*?)```", md, re.S))
    check(not re.search(r"\b(Hint|Branch)\b|hidden :=", code), f"sheet {n}: no Hint/Branch in certificates")
    check('\\"' not in md, f'sheet {n}: no \\" left in question text')
    heads = re.findall(r"^## (.*)$", md, re.M)
    check(len(heads) == len(set(heads)), f"sheet {n}: headings unique")
    bad = [ln for ln in code.splitlines() if re.match(r"\s*·\s*$", ln)]
    check(not bad, f"sheet {n}: no dangling bare bullets")

# 2. Hand-in, Sheet 2 and Sheet 8, with PDF.
for n in (2, 8):
    r = subprocess.run(["python3", "-I", "scripts/export_sheet.py", str(n), "--hand-in", "--progress", str(pf),
                        "--pdf", "--out", str(DIR), "--name", "Test *Student*"], capture_output=True, text=True)
    check(r.returncode == 0, f"sheet {n} hand-in: PDF rendered (exit {r.returncode}) {r.stderr[-300:]}")
    check("Missing character" not in r.stderr, f"sheet {n} hand-in: no missing glyphs")
    md = (DIR / f"sheet{n}-hand-in.md").read_text()
    check("Traceback" not in r.stderr, f"sheet {n} hand-in: no traceback")
    questions = "\n".join(ln for ln in md.splitlines() if not ln.startswith("*Claim.*"))
    check(not re.search(r"\bDecide\b|`left`|`right`|\bNew:|Useful:|inventory", questions),
          f"sheet {n} hand-in: no game instructions in question text")
    if n == 8:
        check("Explanation for Question 1a" in r.stderr or "Question 1a" in r.stderr,
              "sheet 8: broken maths reported by question")
    txt = subprocess.run(["pdftotext", "-layout", str(DIR / f"sheet{n}-hand-in.pdf"), "-"],
                         capture_output=True, text=True).stdout
    flat = re.sub(r"\s+", " ", txt)
    check("✗" in txt, f"sheet {n} PDF: ✗ mark present")
    if n == 2:
        heads = re.findall(r"^## (.*)$", md, re.M)
        check(len(heads) == len(set(heads)), "sheet 2 hand-in: headings unique")
        check(any("part 1 of" in h for h in heads), "sheet 2 hand-in: repeated tag shows its part")
        check("First block" in md and "Second block" in md, "sheet 2: both Explain blocks collected")
        check(md.index("First block") < md.index("Second block"), "sheet 2: Explain blocks in order")
        check("2*x + 3*y" in flat, "sheet 2 PDF: 2*x + 3*y printed literally")
        check("<b>bold?</b>" in flat, "sheet 2 PDF: <b> printed literally")
        check("\\cmd" in flat, "sheet 2 PDF: \\cmd printed literally")
        check("_under_" in flat and "# hash" in flat, "sheet 2 PDF: _ and # literal")
        check("$5" in flat, "sheet 2 PDF: lone $ literal")
        check("→ₗ[ℝ]" in txt, "sheet 2 PDF: →ₗ[ℝ] rendered")
        check("ENDOFLONGLINE" in txt, "sheet 2 PDF: 200-char line wrapped, not clipped")
        check("✓" in txt, "sheet 2 PDF: ✓ mark present")
        check("Test *Student*" in flat, "sheet 2 PDF: name printed literally")
    if n == 8:
        check("sorry" in txt, "sheet 8 PDF: sorry proof printed")
        check("undefinedcontrolsequence" in flat, "sheet 8 PDF: broken maths printed as text")

subprocess.run(["pdftoppm", "-r", "60", "-png", "-f", "1", "-l", "3", str(DIR / "sheet2-hand-in.pdf"),
                str(DIR / "sheet2-page")])
print(f"\n{len(fails)} failure(s). Pages: {DIR}/sheet2-page-*.png")
sys.exit(1 if fails else 0)
PY

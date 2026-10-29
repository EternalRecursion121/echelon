"""Generate the sheet -> level index (Markdown, Lean-string-escaped) from @sheet tags."""
import re, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
order = re.findall(r"^import Game\.Levels\.(\w+)$", (ROOT / "Game.lean").read_text(), re.M)
TAG = re.compile(r"^--\s*@sheet\s+(\d+)\s+Q(\d+)(\S*)", re.M)
rows = {}
for w in order:
    wsrc = (ROOT / 'Game/Levels' / f'{w}.lean').read_text()
    wtitle = re.search(r'^Title "((?:[^"\\]|\\.)*)"', wsrc, re.M).group(1)
    for f in sorted((ROOT / 'Game/Levels' / w).glob('L*.lean')):
        s = f.read_text()
        lvl = re.search(r'^Level (\d+)', s, re.M).group(1)
        title = re.search(r'^Title "((?:[^"\\]|\\.)*)"', s, re.M).group(1)
        for m in TAG.finditer(s):
            sh, q, part = int(m.group(1)), int(m.group(2)), m.group(3)
            rows.setdefault(sh, []).append((q, part, wtitle, int(lvl), title))
# Sheet questions without lettered parts that the game splits into tagged parts Q7a, Q7b, …
# (keep in sync with UNLETTERED in scripts/export_sheet.py): shown as "Q7 (part 1 of 3)".
UNLETTERED = {8: {6}, 9: {7, 8}, 10: {2, 6}}
out = []
for sh in sorted(rows):
    rs = sorted(rows[sh], key=lambda r: (r[0], r[1], r[3]))
    def label(q, p):
        if q in UNLETTERED.get(sh, ()):
            same = [r for r in rs if r[0] == q]
            i = next(k for k, r in enumerate(same) if r[1] == p) + 1
            return f'Q{q} (part {i} of {len(same)})'
        return f'Q{q}{p}'
    out.append(f'**Sheet {sh}.** ' + ' · '.join(f'{label(q, p)}: {w} {l}' for q, p, w, l, t in rs))
    out.append('')
print('\n'.join(out))

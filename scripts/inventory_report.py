#!/usr/bin/env python3
"""Report inventory problems across the whole game (world order from Game.lean imports):

- items introduced (NewTactic/NewTheorem/NewDefinition) in more than one level;
- items used in a level before the level that introduces them (backward use → engine loops).

"Used" = the item's name occurs as a whole word in the level's proof (from `Statement` to
`Conclusion`), excluding Hint strings. Use --fix to move each introduction to the earliest
level that uses it (removing the later duplicates).
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEVELS = ROOT / "Game" / "Levels"
KINDS = ("NewTactic", "NewHiddenTactic", "NewTheorem", "NewDefinition")

order = re.findall(r"^import Game\.Levels\.(\w+)$", (ROOT / "Game.lean").read_text(), re.M)
seq = [f for w in order for f in sorted((LEVELS / w).glob("L*.lean"))]
pos = {f: i for i, f in enumerate(seq)}

intro = {}     # (kind_family, item) -> list of files
for f in seq:
    for kind, line in re.findall(r"^(New(?:Hidden)?Tactic|NewTheorem|NewDefinition) (.*)$", f.read_text(), re.M):
        fam = "tac" if "Tactic" in kind else kind
        for it in line.split():
            intro.setdefault((fam, it.strip("«»")), []).append((f, kind))


def proof_text(src):
    m = re.search(r"^Statement.*?(?=^Conclusion|\Z)", src, re.S | re.M)
    t = m.group(0) if m else ""
    t = re.sub(r'Hint[^"\n]*"(?:[^"\\]|\\.)*"', "", t, flags=re.S)
    return t


def uses(f, item):
    t = proof_text(f.read_text())
    short = item.split(".")[-1]
    pat = re.escape(item) if "." in item else re.escape(short)
    return re.search(r"(?<![\w.])" + pat + r"(?![\w'₀-₉])", t) is not None


problems = []
for (fam, item), where in sorted(intro.items(), key=lambda kv: kv[0][1]):
    first_intro = min(pos[f] for f, _ in where)
    users = [f for f in seq if uses(f, item)]
    earliest_use = min((pos[f] for f in users), default=None)
    target = first_intro if earliest_use is None else min(first_intro, earliest_use)
    if len(where) > 1 or target < first_intro:
        problems.append((fam, item, where, seq[target]))

for fam, item, where, target in problems:
    print(f"{item:45} introduced in {', '.join(str(f.relative_to(LEVELS)) for f, _ in where)}"
          f" → should be {target.relative_to(LEVELS)}")
print(f"{len(problems)} items to fix")

if "--fix" in sys.argv:
    for fam, item, where, target in problems:
        kind = where[0][1] if fam != "tac" else ("NewHiddenTactic" if all(k == "NewHiddenTactic" for _, k in where) else "NewTactic")
        for f, k in where:
            s = f.read_text()
            def drop(m):
                items = [x for x in m.group(2).split() if x.strip("«»") != item]
                return f"{m.group(1)} {' '.join(items)}" if items else ""
            s = re.sub(rf"^({k}) (.*)$", lambda m: drop(m) if item in [x.strip('«»') for x in m.group(2).split()] else m.group(0), s, flags=re.M)
            f.write_text(s)
        s = target.read_text().rstrip("\n")
        name = f"«{item}»" if item in ("have", "calc", "module", "show", "exact?") else item
        target.write_text(s + f"\n{kind} {name}\n")
    print("fixed")

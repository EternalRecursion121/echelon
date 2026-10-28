#!/usr/bin/env python3
"""Read MakeGame's "A depends on B because of [items]" errors from a build log; where B comes
after A in Game.lean's import order, move each item's introduction to the first level of A
that mentions it (by short name), or A's first level. Usage: fix_backward_deps.py build.log"""
import re, sys, pathlib
ROOT = pathlib.Path(__file__).resolve().parent.parent
LEVELS = ROOT / "Game" / "Levels"
order = re.findall(r"^import Game\.Levels\.(\w+)$", (ROOT / "Game.lean").read_text(), re.M)
log = pathlib.Path(sys.argv[1]).read_text()
moved = 0
for a, b, items in re.findall(r"(\w+) depends on (\w+) because of \[([^\]]*)\]", log, re.S):
    if a not in order or b not in order or order.index(b) < order.index(a):
        continue
    for item in [x.strip() for x in items.replace("\n", " ").split(",") if x.strip()]:
        short = item.split(".")[-1]
        # find and remove the introduction in world b
        kind = None
        for f in sorted((LEVELS / b).glob("L*.lean")):
            s = f.read_text()
            def drop(m):
                nonlocal_kind.append(m.group(1))
                rest = [x for x in m.group(2).split() if x.strip("«»") != item]
                return f"{m.group(1)} {' '.join(rest)}" if rest else ""
            nonlocal_kind = []
            s2 = re.sub(r"^(New(?:Hidden)?Tactic|NewTheorem|NewDefinition) (.*)$",
                        lambda m: drop(m) if item in [x.strip("«»") for x in m.group(2).split()] else m.group(0),
                        s, flags=re.M)
            if s2 != s:
                f.write_text(s2); kind = nonlocal_kind[0]
        if kind is None:
            print(f"? {item}: no introduction found in {b}"); continue
        target = None
        for f in sorted((LEVELS / a).glob("L*.lean")):
            if re.search(r"(?<![\w])" + re.escape(short) + r"(?![\w'])", f.read_text()):
                target = f; break
        target = target or sorted((LEVELS / a).glob("L*.lean"))[0]
        name = f"«{item}»" if item in ("have", "calc", "module", "show") else item
        target.write_text(target.read_text().rstrip("\n") + f"\n{kind} {name}\n")
        print(f"moved {kind} {item}: {b} → {target.relative_to(LEVELS)}"); moved += 1
print(f"{moved} moved")

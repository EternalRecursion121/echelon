#!/usr/bin/env python3
"""Flag sheet questions that are only reachable after LATER sheets' questions.

A level tagged `@sheet N` is reachable once every ancestor world is complete (Dependency edges
in Game.lean plus the engine-computed edges in .lake/gamedata/game.json) and every earlier level
of its own world is solved. If any of those prerequisite levels is tagged with a sheet > N, a
student handing in sheet N is forced through later-sheet material first.

Usage: python3 scripts/sheet_order.py [--same-world] [--strict]
  default: report levels whose ancestor worlds hold later-sheet levels
  --same-world: also report earlier levels of the same world (the engine gates those too)
  --strict: exit 1 if anything is reported (the default exit is 0: most reports are the
            known one-sheet interleaves of the lecture-order world map, see round7-fixes.md)
"""
import json, re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
TAG = re.compile(r"^--\s*@sheet\s+(\d+)\s+Q(\S+)", re.M)

edges = set(re.findall(r"^Dependency\s+(\w+)\s*→\s*(\w+)", (ROOT / "Game.lean").read_text(), re.M))
gj = ROOT / ".lake" / "gamedata" / "game.json"
if gj.exists():
    edges |= {tuple(e) for e in json.loads(gj.read_text())["worlds"]["edges"]}
parents = {}
for a, b in edges:
    parents.setdefault(b, set()).add(a)


def ancestors(w):
    seen, todo = set(), [w]
    while todo:
        for p in parents.get(todo.pop(), ()):
            if p not in seen:
                seen.add(p)
                todo.append(p)
    return seen


tagged = {}   # world -> [(level, sheet, q)]
for f in sorted((ROOT / "Game" / "Levels").rglob("L*.lean")):
    src = f.read_text()
    w = re.search(r'^World\s+"([^"]+)"', src, re.M)
    l = re.search(r"^Level\s+(\d+)", src, re.M)
    for m in TAG.finditer(src):
        tagged.setdefault(w.group(1), []).append((int(l.group(1)), int(m.group(1)), m.group(2)))

flags, info = [], []
for w, levels in sorted(tagged.items()):
    anc = ancestors(w)
    before = [(s, f"{aw} L{al} (S{s} Q{q})") for aw in anc for al, s, q in tagged.get(aw, [])]
    for lvl, sheet, q in sorted(levels):
        later = sorted(x for x in before if x[0] > sheet)
        if later:
            flags.append(f"S{sheet} Q{q} ({w} L{lvl}) needs ancestor-world levels of later sheets: "
                         + ", ".join(d for _, d in later[-3:]) + (" …" if len(later) > 3 else ""))
        same = [f"L{ol} (S{os} Q{oq})" for ol, os, oq in levels if ol < lvl and os > sheet]
        if same:
            info.append(f"S{sheet} Q{q} ({w} L{lvl}) comes after same-world " + ", ".join(same))

print(f"{len(flags)} sheet-order problem(s) across worlds")
for x in flags:
    print("  " + x)
if "--same-world" in sys.argv:
    print(f"{len(info)} within-world ordering note(s)")
    for x in info:
        print("  " + x)
sys.exit(1 if "--strict" in sys.argv and (flags or ("--same-world" in sys.argv and info)) else 0)

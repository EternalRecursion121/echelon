#!/usr/bin/env python3
"""Print what a player sees for a level — without the sample proof.

Usage: python3 scripts/player_view.py Game/Levels/<World>/<Lnn_Name>.lean
Shows: world/level/title, Introduction, the claim (docstring) and Lean statement, visible
hints (first line of each; hidden hints are listed separately as "on request"), and the
level's New/Disabled inventory lines. Hints are context-dependent in the real game: they
appear when your goal matches the point in the sample proof where they were placed.
"""
import re, sys, pathlib

src = pathlib.Path(sys.argv[1]).read_text()
def grab(key):
    m = re.search(key + r'\s+"((?:[^"\\]|\\.)*)"', src, re.S)
    return m.group(1).replace("\\\\", "\\").replace('\\"', '"').strip() if m else ""
w = re.search(r'^World "([^"]+)"', src, re.M); l = re.search(r"^Level (\d+)", src, re.M)
print(f"# {w.group(1) if w else '?'} — Level {l.group(1) if l else '?'}: {grab('Title')}\n")
print(grab("Introduction"), "\n")
m = re.search(r"(/--(?:(?!-/).)*-/)?\s*Statement(.*?):=\s*by", src, re.S)
if m:
    if m.group(1): print("Claim:", m.group(1)[3:-2].strip())
    print("Lean statement:\nStatement" + m.group(2).rstrip() + " := by\n")
visible, hidden = [], []
for hm in re.finditer(r"Hint\s*(\([^)]*\))?\s*\"((?:[^\"\\]|\\.)*)\"", src, re.S):
    text = " ".join(hm.group(2).split()).replace("\\\\", "\\")
    (hidden if hm.group(1) and "hidden" in hm.group(1) else visible).append(text)
print("Visible hints (shown when your goal matches):"); [print("  -", h) for h in visible]
print(f"Hidden hints available on request: {len(hidden)}")
print()
for line in re.findall(r"^((?:New|Disabled|Only)\w+ .*)$", src, re.M):
    print(line)

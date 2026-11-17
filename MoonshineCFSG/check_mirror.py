#!/usr/bin/env python3
"""Check that MoonshineCFSG's copies of VOA Moonshine modules match the library.

Every `MoonshineCFSG/MoonshineCFSG/X.lean` (except the bridge) is a copy of `VOA/Moonshine/X.lean` with import lines
of copied modules renamed `VOA.Moonshine.Y` -> `MoonshineCFSG.Y`. The nine Route A files differ in substance (they use
CFSG's Monster structures); for them this script only reports the size of the difference. Exit code 1 if any other
copy has drifted from its library original, or if an original is missing.

Usage (from the repository root):  python3 MoonshineCFSG/check_mirror.py
"""
import difflib
import os
import re
import sys

ROUTE_A = {
    "MonsterGriess.Golay", "MonsterGriess.GriessTrilinear", "MonsterGriess.LatticeFamilies", "MonsterGriess.Short",
    "MonsterGriess.SpinExtraspecial", "MonsterGriess.SpinGroupQ", "MonsterGriess.TrialityLabels",
    "MonsterGriess.VisibleAction", "MoonshineLRLiftXi",
}
BRIDGE = "MoonshineLRCFSGBridge"
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SUB = os.path.join(ROOT, "MoonshineCFSG", "MoonshineCFSG")
IMPORT = re.compile(r"^(\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?)MoonshineCFSG\.(\S+)(.*)$")


def unrename(text: str) -> str:
    return "\n".join(
        (m.group(1) + "VOA.Moonshine." + m.group(2) + m.group(3)) if (m := IMPORT.match(line)) else line
        for line in text.split("\n")
    )


def main() -> int:
    drifted, missing, route_a, same = [], [], [], 0
    for dirpath, _, files in os.walk(SUB):
        for name in files:
            if not name.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dirpath, name), SUB)[:-5]
            mod = rel.replace(os.sep, ".")
            if mod == BRIDGE:
                continue
            orig = os.path.join(ROOT, "VOA", "Moonshine", rel + ".lean")
            if not os.path.exists(orig):
                missing.append(mod)
                continue
            a = open(orig, encoding="utf-8").read()
            b = unrename(open(os.path.join(dirpath, name), encoding="utf-8").read())
            if a == b:
                same += 1
                continue
            n = sum(1 for d in difflib.unified_diff(a.split("\n"), b.split("\n"), lineterm="", n=0)
                    if d[:1] in "+-" and not d.startswith(("+++", "---")))
            (route_a if mod in ROUTE_A else drifted).append((mod, n))
    print(f"identical modulo import renaming: {same}")
    for mod, n in sorted(route_a):
        print(f"Route A (expected to differ): {mod}: {n} changed lines")
    for mod in sorted(missing):
        print(f"MISSING library original: VOA/Moonshine/{mod.replace('.', '/')}.lean")
    for mod, n in sorted(drifted):
        print(f"DRIFTED from library: {mod}: {n} changed lines")
    return 1 if (drifted or missing) else 0


if __name__ == "__main__":
    sys.exit(main())

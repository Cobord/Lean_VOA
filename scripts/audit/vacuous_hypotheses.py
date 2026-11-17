#!/usr/bin/env python3
"""Textual audit: declarations whose hypotheses range over a type the library itself proves EMPTY.

A theorem with a hypothesis of an empty type is vacuous (from that hypothesis one gets `False`, hence
anything).  This script keeps a registry of the types the library proves uninhabited (each entry names
the Lean theorem that proves it), scans every `theorem`/`lemma`/`def` signature in `VOA/` (the text
between the declaration keyword and `:=`), and lists the declarations whose signature mentions a
registered type.  It then checks that none of the README headline declarations is among them.

This is a text scan: it can over-report (a mention that is not a hypothesis, e.g. a return type) and
it does not follow definitions that unfold to a registered type.  An exact check needs a dependency
walk of the compiled library (`scripts/audit/HeadlineHypotheses.lean`).

Usage:  python3 scripts/audit/vacuous_hypotheses.py [--list]
Exit code 1 if a README headline mentions a registered empty type.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# type pattern  ->  (theorem proving emptiness, scope note)
REGISTRY = {
    r"\bInducedAssignment\b(?!\.)": ("VOA.not_nonempty_inducedAssignment", "every W"),
    r"\bFaithfulScorecard\b": ("VOA.not_nonempty_faithfulScorecard", "every W"),
    r"\bCarrierBridgeFamily\b": ("VOA.VHat.CarrierBridgeFamily.false", "every W"),
    r"\bCarrierBridgeDataFamily\b": ("VOA.VHat.CarrierBridgeDataFamily.false", "every W"),
    r"\bGenFields \(MRbot \(virasoroOPE": ("VOA.NonlinearConformal.not_nonempty_genFields_MRbot_virasoro", "Virasoro"),
    r"\bGradedImpliesRegular LQ43\.L43\b": ("oldHeadline_hypothesis_unsatisfiable", "L43 only"),
    r"\bGradedImpliesPoleZero LQ43\.L43\b": ("oldHeadline_weakened_hypothesis_unsatisfiable", "L43 only"),
}
# `Unitary N` is empty only when `M` has two independent vectors (`old_unitary_isEmpty`); reported
# separately as conditional.
CONDITIONAL = {r"\bUnitary \w+\b": ("old_unitary_isEmpty", "empty when dim M ≥ 2")}

HEADLINES = [
    "zhuModularity_pinned_of_C2Cofinite_voaPBW", "finrank_analyticBlocks_le_card_Φ",
    "onePointSubexp_of_c2", "strictSpanning_of_C2Cofinite", "simpleAModsRealized_of_C2Cofinite",
    "zhuBijective", "borcherds", "heisenbergVOA", "virasoroVOA", "affineSl2VOA_closed",
    "latticeVOAGen", "affineSl3VOA", "simpleVOA", "moonshine", "minimal_graded_rigidity",
    "L43_graded_rigidity", "levelOne_coe_mem_E46", "subexponential_of_majorant_recursion",
    "finiteDimensional_A_of_C2Cofinite", "monstrousMoonshine",
]

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(theorem|lemma|def|abbrev)\s+([^\s(:{\[]+)", re.M)


def signatures():
    for d, _, fs in os.walk(os.path.join(ROOT, "VOA")):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(d, f)
            text = open(p, encoding="utf-8").read()
            for m in DECL.finditer(text):
                end = text.find(":=", m.end())
                if end < 0:
                    continue
                sig = text[m.end():end]
                yield os.path.relpath(p, ROOT), text.count("\n", 0, m.start()) + 1, m.group(2), sig


def main():
    hits, cond = [], []
    for path, line, name, sig in signatures():
        for pat, (thm, scope) in REGISTRY.items():
            if re.search(pat, sig):
                hits.append((path, line, name, pat, thm, scope))
        for pat, (thm, scope) in CONDITIONAL.items():
            if re.search(pat, sig):
                cond.append((path, line, name, thm, scope))
    by_type = {}
    for h in hits:
        by_type.setdefault(h[4], []).append(h)
    print(f"Declarations whose signature mentions a type the library proves EMPTY: {len(hits)}")
    for thm, hs in sorted(by_type.items(), key=lambda kv: -len(kv[1])):
        files = len({h[0] for h in hs})
        print(f"  {thm}: {len(hs)} declarations in {files} files")
    print(f"Mentions of conditionally empty `Unitary`: {len(cond)}")
    bad = [h for h in hits if h[2].split(".")[-1] in HEADLINES]
    print(f"README headlines among them: {len(bad)}")
    for h in bad:
        print(f"  !! {h[2]}  ({h[0]}:{h[1]})  via {h[4]}")
    if "--list" in sys.argv:
        for h in sorted(hits):
            print(f"{h[0]}:{h[1]}\t{h[2]}\t{h[4]}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

/-
Non-vacuity witnesses for the README headline results (audit probe; not part of `lake build`).

A clean `#print axioms` does not show that a theorem's hypotheses can be met.  For each headline with
nontrivial hypotheses we instantiate it at a concrete VOA — the rank-one lattice VOA `V_{2m}` — with
EVERY hypothesis discharged by a library theorem, so that the conclusion is reached unconditionally
for at least one object.  Together with the existing unconditional instances
(`zhuModularity_V2m`, `zhuModularity_V2mPlus`, `zhuModularity_cubicModel`,
`trivialVOA_zhuModularity_closed`) this rules out the "unsatisfiable hypothesis bundle" failure mode
for these headlines.  It does NOT certify conclusion strength (see README §2, "Auditing a headline
result").

Run (from the repository root, after building the imports):
  lake env lean -DmaxSynthPendingDepth=3 scripts/audit/HeadlineNonVacuity.lean
-/
import VOA.Classification.COne.LatticeC2
import VOA.Classification.COne.LatticeStronglyRational
import VOA.Classification.COne.LatticeSimple
import VOA.Classification.COne.McRaeO1FinitePhi
import VOA.Modularity.ZhuModularityRational
import VOA.Modularity.GNProp8Closure
import VOA.Modularity.ZhuBlockCount
import VOA.Modularity.BlockGrowth
import VOA.Modularity.ZhuAlgebraFinite
import VOA.Modules.ZhuVermaAnArchLUBijection
import VOA.Modules.ZhuVermaAnArchDLM3PBWAxiom
import VOA.Examples.ZhuInstantiation

open VOA VOA.Classification.COne VOA.VHat.DLM3

namespace VOA.HeadlineNonVacuity

variable (m : ℕ) (hm : 1 ≤ m)

/-- `C₂`-cofiniteness of `V_{2m}`. -/
theorem c2 : C2Cofinite (V2m m hm) := V2m_c2Cofinite m hm

/-- Headline: Gaberdiel–Neitzke strict spanning, at `V_{2m}`. -/
noncomputable def strictSpanning_V2m : StrictSpanning (V2m m hm) :=
  strictSpanning_of_C2Cofinite _ (c2 m hm)

/-- Headline: finite-dimensionality of `A(V_{2m})`. -/
theorem finiteDimensional_A_V2m : FiniteDimensional ℂ (A (V2m m hm)) :=
  finiteDimensional_A_of_C2Cofinite (V2m m hm) (c2 m hm)

/-- Headline: realization of simple `A(V_{2m})`-modules (the `BottomProjection` input is supplied
by `voaPBWBottomProjection`, which exists for every parabolic representation). -/
theorem simpleAModsRealized_V2m : SimpleAModsRealized (V2m m hm) :=
  simpleAModsRealized_of_C2Cofinite (c2 m hm) (voaPBWBottomProjection _)

/-- Headline: Zhu's correspondence (uniqueness half), at `V_{2m}`. -/
theorem zhuBijective_V2m : Function.Bijective (forwardMapIrr (V2m m hm)) :=
  zhuBijective (voaPBWBottomProjection _)

/-- Headline: the genus-one block count, at `V_{2m}`, every hypothesis discharged. -/
theorem finrank_analyticBlocks_V2m :
    letI : Finite (Φ (V2m m hm)) := VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw (c2 m hm)
    Module.finrank ℂ (Submodule.map restrictImGT (analyticBlocks (V2m m hm)))
      ≤ Nat.card (Φ (V2m m hm)) :=
  letI : Finite (Φ (V2m m hm)) := VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw (c2 m hm)
  finrank_analyticBlocks_le_card_Φ (V2m m hm) (vacuumGradeZero_holds (V2m m hm)) (c2 m hm)
    (isSemisimpleRing_A_of_rational (V2m_stronglyRational m hm).rational)
    (simpleAModsRealized_V2m m hm) (voaPBWBottomProjection _)

/-- Headline: convergence of the `q`-trace, at the adjoint module of `V_{2m}`. -/
theorem onePointSubexp_V2m :
    OnePointSubexp (adjointModule (V2m m hm)) (0 - (V2m m hm).centralCharge / 24) :=
  onePointSubexp_of_c2 (V2m m hm) (adjointModule (V2m m hm))
    (adjoint_hasConformalWeight _ (V2m_isSimple m hm).vacuum_ne_zero)
    (vacuumGradeZero_holds (V2m m hm)) (c2 m hm)

end VOA.HeadlineNonVacuity

#print axioms VOA.HeadlineNonVacuity.strictSpanning_V2m
#print axioms VOA.HeadlineNonVacuity.finiteDimensional_A_V2m
#print axioms VOA.HeadlineNonVacuity.simpleAModsRealized_V2m
#print axioms VOA.HeadlineNonVacuity.zhuBijective_V2m
#print axioms VOA.HeadlineNonVacuity.finrank_analyticBlocks_V2m
#print axioms VOA.HeadlineNonVacuity.onePointSubexp_V2m

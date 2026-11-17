import VOA.Moonshine.MoonshineCNRootSpaces

/-! Equivariance of the actual root-space identification. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open AutMonster

-- Lean 4.35 port: newer Mathlib makes the commutator Lie ring of an associative ring a local instance only.
attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] vnatStringWeightAddCommGroup vnatStringSliceAddCommGroup
attribute [local instance] monsterPhysicalAddCommGroup

theorem monsterLieSectorQuotientEquiv_equivariant (x y : ℤ) (a : Fin 2) (g : AutVnat)
    (u : (vnatStringModule x y a).weightRadicalQuotient (vnatStringModule x y a).physical 1) :
    (monsterLieSectorQuotientEquiv x y a
      ((vnatStringGroupAction x y a).stableWeightQuotientAction _
        (vnatStringGroupAction x y a).action_preserves_physical 1 g u) : monsterLieAlgebra) =
      monsterLieAut g (monsterLieSectorQuotientEquiv x y a u) := by
  induction u using Submodule.Quotient.induction_on with
  | _ u =>
    change monsterLieProjection (moonshineMatterPhysicalSectorMap x y a
      ((vnatStringGroupAction x y a).stableWeightAction _
        (vnatStringGroupAction x y a).action_preserves_physical 1 g u)) =
      monsterLieAut g (monsterLieProjection (moonshineMatterPhysicalSectorMap x y a u))
    exact (congrArg monsterLieProjection
      (Subtype.ext (moonshineMatterSectorEquiv_equivariant g ![x, y] u.val.val))).trans
      (monsterLieAut_mk g (moonshineMatterPhysicalSectorMap x y a u)).symm

theorem monsterLieSectorQuotientEquiv_symm_equivariant (x y : ℤ) (a : Fin 2)
    (g : AutVnat) (u : monsterLieMomentum ![x, y]) :
    (monsterLieSectorQuotientEquiv x y a).symm
      ⟨monsterLieAut g u, monsterLieAut_momentum g _ u u.property⟩ =
      (vnatStringGroupAction x y a).stableWeightQuotientAction _
        (vnatStringGroupAction x y a).action_preserves_physical 1 g
          ((monsterLieSectorQuotientEquiv x y a).symm u) := by
  apply (monsterLieSectorQuotientEquiv x y a).symm_apply_eq.mpr
  apply Subtype.ext
  have he := monsterLieSectorQuotientEquiv_equivariant x y a g
    ((monsterLieSectorQuotientEquiv x y a).symm u)
  exact (congrArg (fun v : monsterLieMomentum ![x, y] => monsterLieAut g v)
    ((monsterLieSectorQuotientEquiv x y a).apply_symm_apply u)).symm.trans he.symm

/-- The action is the existing restriction of Aut(V♮), with no additional hypotheses. -/
theorem monsterLieRootSpaceEquiv_equivariant (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0)
    (g : AutVnat) (u : monsterLieMomentum ![x, y]) :
    monsterLieRootSpaceEquiv x y h
      ⟨monsterLieAut g u, monsterLieAut_momentum g _ u u.property⟩ =
      GriessAut.autRestrict g (1 - x * y) (monsterLieRootSpaceEquiv x y h u) := by
  -- Lean 4.35 port: the `simp only` unfolding timed out in `whnf`; compose the two
  -- equivariance facts as terms (`LinearEquiv.trans_apply` is definitional).
  have h1 := monsterLieSectorQuotientEquiv_symm_equivariant x y (stringSectorFamily x y h) g u
  have h2 := stringSectorNoGhostEquiv_equivariant x y h g
    ((monsterLieSectorQuotientEquiv x y (stringSectorFamily x y h)).symm u)
  exact (congrArg (stringSectorNoGhostEquiv x y h) h1).trans h2

end VOA.Moonshine.ConwayNorton

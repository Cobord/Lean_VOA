import VOA.Classification.COne.OrbC2fCoordinates
import VOA.Classification.COne.OrbC2fTransport
import VOA.Classification.COne.OrbC2fIterate

/-! # Cubic fixedness of the existing norm-eight seeds

The automorphism is the transport of `kleinCubic` through the concrete
sublattice embedding. No generator-action equation is an input.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2f
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 LatMod OrbC2c OrbC2e OrbC2b

/-- The explicit equivalence whose underlying ambient map is `scaleMorph 1 2`. -/
def plusToKlein : VP 4 four_ge_one ≃ₗ[ℂ] (orbifold klein).carrier :=
  (Submodule.equivMapOfInjective _ (scaleMorph_injective 1 le_rfl 2)
    (VP 4 four_ge_one)).trans (LinearEquiv.ofEq _ _ (map_scaleMorph_plus 1 le_rfl 2))

theorem plusToKlein_val (v : VP 4 four_ge_one) :
    (plusToKlein v : LatModuleGen (latP 1)) = scaleMorph 1 2 v := rfl

theorem plusToKlein_hom : IsVOAHom (V2mPlus 4 four_ge_one)
    (orbifoldVOA klein) plusToKlein.toLinearMap := by
  have hf := scaleMorph_isVOAHom 1 le_rfl 2
  constructor
  · apply Subtype.ext
    exact hf.map_vacuum
  · intro a n b
    apply Subtype.ext
    exact hf.map_smul a n b

theorem plusToKlein_omega : plusToKlein (V2mPlus 4 four_ge_one).conformalVector =
    (orbifoldVOA klein).conformalVector := by
  apply Subtype.ext
  exact scaleMorph_omega 1 le_rfl 2

theorem plusToKlein_smul (a b : VP 4 four_ge_one) (n : ℤ) :
    plusToKlein ((V2mPlus 4 four_ge_one).smul a n b) =
      (orbifoldVOA klein).smul (plusToKlein a) n (plusToKlein b) :=
  plusToKlein_hom.map_smul a n b

theorem plusToKlein_vacuum : plusToKlein (V2mPlus 4 four_ge_one).vacuum =
    (orbifoldVOA klein).vacuum := plusToKlein_hom.map_vacuum

/-- The actual cubic automorphism on V₈⁺. -/
def plusCubic : Aut (V2mPlus 4 four_ge_one) where
  toLinearEquiv := plusToKlein.trans (kleinCubic.toLinearEquiv.trans plusToKlein.symm)
  map_smul' a n b := by
    apply plusToKlein.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [plusToKlein_smul, kleinCubic.map_smul', plusToKlein_smul]
    simp only [LinearEquiv.apply_symm_apply]
  map_vacuum := by
    apply plusToKlein.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      plusToKlein_vacuum, kleinCubic.map_vacuum]
  map_omega := by
    apply plusToKlein.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      plusToKlein_omega, kleinCubic.map_omega]

theorem plusCubic_intertwine (v : VP 4 four_ge_one) :
    plusToKlein (plusCubic v) = kleinCubic (plusToKlein v) :=
  plusToKlein.apply_symm_apply _

theorem plusCubic_cube : plusCubic ^ 3 = 1 := by
  apply Aut.ext
  apply LinearEquiv.ext
  intro v
  apply plusToKlein.injective
  change plusToKlein (plusCubic (plusCubic (plusCubic v))) = plusToKlein v
  rw [plusCubic_intertwine, plusCubic_intertwine, plusCubic_intertwine]
  change (kleinCubic ^ 3) (plusToKlein v) = plusToKlein v
  rw [kleinCubic_cube, Aut.one_apply]

theorem plusToKlein_J : (plusToKlein (J 4 four_ge_one) : LatModuleGen (latP 1)) =
    cubicJ := by rw [plusToKlein_val, scaleMorph_J, cubicJ_eq_neutral]

theorem plusToKlein_E : (plusToKlein (EP 4 four_ge_one) : LatModuleGen (latP 1)) =
    cubicE := by rw [plusToKlein_val, scaleMorph_E, cubicE_eq_charges]

/-- Both action formulas hold for the actual transported cubic. -/
theorem plusCubic_generators :
    plusCubic (J 4 four_ge_one) = (-1/2 : ℂ) • J 4 four_ge_one +
      (9/2 : ℂ) • EP 4 four_ge_one ∧
    plusCubic (EP 4 four_ge_one) = (-1/6 : ℂ) • J 4 four_ge_one +
      (-1/2 : ℂ) • EP 4 four_ge_one := by
  constructor
  all_goals
    apply plusToKlein.injective
    rw [plusCubic_intertwine, map_add, map_smul, map_smul]
    apply Subtype.ext
    change rotC _ = _
    simp only [Submodule.coe_add, Submodule.coe_smul, plusToKlein_J, plusToKlein_E]
  · exact rotC_cubic_generators.1
  · exact rotC_cubic_generators.2

/-- The transported action has exact order three, not merely order dividing three. -/
theorem plusCubic_ne_one : plusCubic ≠ 1 := by
  classical
  intro hg
  have he := plusCubic_generators.2
  rw [hg, Aut.one_apply] at he
  have he' := congrArg (fun v => (plusToKlein v : LatModuleGen (latP 1))) he
  simp only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul,
    plusToKlein_E, plusToKlein_J] at he'
  rw [cubicE_eq_charges, cubicJ_eq_neutral] at he'
  -- 4.35: `coordEα_apply` no longer fires inside `norm_num` on ℤ-typed charges; evaluate
  -- the three coordinates explicitly.
  have hA : coordEα (latP 1) ((2 : ℤ) : (latP 1).carrier) (latChargeGen (latP 1) (2 : ℤ)) =
      vacuumN (latP 1).rank :=
    (coordEα_apply (latP 1) _ _ _).trans (if_pos rfl)
  have hB : coordEα (latP 1) ((2 : ℤ) : (latP 1).carrier) (latChargeGen (latP 1) (-2 : ℤ)) =
      0 :=
    (coordEα_apply (latP 1) _ _ _).trans
      (if_neg (by intro h; have hh : (2 : ℤ) = -2 := h; omega))
  have hC : coordEα (latP 1) ((2 : ℤ) : (latP 1).carrier) (ls 1 JR) = 0 :=
    (coordEα_apply (latP 1) _ _ _).trans
      (if_neg (by intro h; have hh : (2 : ℤ) = 0 := h; omega))
  have hc := congrArg (coordEα (latP 1) ((2 : ℤ) : (latP 1).carrier)) he'
  simp only [map_add, map_smul, hA, hB, hC, smul_zero, add_zero, zero_add] at hc
  have h3 : (3 / 2 : ℂ) • vacuumN (latP 1).rank = 0 := by
    linear_combination (norm := module) hc
  have h0 : vacuumN (latP 1).rank = 0 :=
    (smul_eq_zero.mp h3).resolve_left (by norm_num)
  exact (one_ne_zero : vacuumN (latP 1).rank ≠ 0) h0

theorem plusCubic_order : orderOf plusCubic = 3 :=
  orderOf_eq_prime plusCubic_cube plusCubic_ne_one

theorem weightNine_fixed : plusCubic weightNine = weightNine :=
  weightNine_fixed_of_action plusCubic plusCubic_generators.1 plusCubic_generators.2

theorem weightSixteen_fixed : plusCubic weightSixteen = weightSixteen :=
  weightSixteen_fixed_of_action plusCubic plusCubic_generators.1 plusCubic_generators.2

end VOA.Classification.COne.OrbC2f

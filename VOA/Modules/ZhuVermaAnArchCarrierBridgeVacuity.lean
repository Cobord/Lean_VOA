/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCarrierBridgeBuild

/-!
# The carrier-bridge families are uninhabited (vacuity of the MU-track inputs)

`VHat.CarrierBridgeFamily W` and `VHat.CarrierBridgeDataFamily W` ask, for every bottom module
`U : AMod W`, for a `𝒱`-equivariant isomorphism `M̄(U) ≅ MU W U` (a `CarrierBridge`), together with
vacuum normalisation on the target (`hvac`: `1₍₋₁₎ = id`) and a nonzero bottom (`hbot`).

**Both structures are empty, for every `W`.**  The carrier `M̄(U) = (U(V̂) ⊗ U) ⧸ D` imposes no
vacuum normalisation: in `U(V̂)` the vacuum mode `1₍₋₁₎` is a free generator, not the unit.  The
augmentation `ε : U(V̂) → ℂ` (killing every mode) gives `ε ⊗ id : U(V̂) ⊗ U → U`, whose kernel
contains every defect vector and is `V̂`-invariant, so it descends to `augBar : M̄(U) → U`, and
`augBar` kills the image of every mode.  If `1₍₋₁₎` acted as the identity on `M̄(U)` (which an
equivariant bridge to a target with `hvac` forces), then `u = augBar [1 ⊗ u] = augBar (1₍₋₁₎ [1 ⊗ u])
= 0` for every `u`, so `U = 0`, hence `M̄(U) = 0`, hence `MU W U = 0`, contradicting `hbot`.
`AMod W` always contains the zero module, so no family exists.

Consequently every theorem whose hypotheses include a `CarrierBridgeFamily` or a
`CarrierBridgeDataFamily` (the superseded MU track: `headline_zhuBijection_of_bridge`,
`zhuBijection_of_bridgeData`, `zhuBijection_trophy`, …) is **vacuous**.  This file records that
fact in Lean so that it cannot be overlooked; it is not used by any headline result.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped TensorProduct

-- Lean 4.35 port: Mathlib `b63f6e8a` makes `LieRing.ofAssociativeRing` a def; on v4.30 this is a no-op.
attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The augmentation and its descent to `M̄(U)` -/

/-- The augmentation `ε : U(V̂) →ₐ ℂ`, the lift of the zero Lie morphism: it kills every mode. -/
noncomputable def uAug (W : VertexOperatorAlgebra 𝒱) : UEnv W →ₐ[ℂ] ℂ :=
  UniversalEnvelopingAlgebra.lift ℂ (0 : VHatCarrier W →ₗ⁅ℂ⁆ ℂ)

theorem uAug_uι (x : VHatCarrier W) : uAug W (uι W x) = 0 := by
  simp only [uAug, uι]
  exact UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ x

/-- `ε ⊗ id : U(V̂) ⊗ M → M`. -/
noncomputable def augT (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M] [Module ℂ M] :
    UEnv W ⊗[ℂ] M →ₗ[ℂ] M :=
  (TensorProduct.lid ℂ M).toLinearMap ∘ₗ TensorProduct.map (uAug W).toLinearMap LinearMap.id

theorem augT_tmul (e : UEnv W) (y : M) : augT W M (e ⊗ₜ[ℂ] y) = uAug W e • y := by
  simp [augT]

/-- The free action lands in the kernel of the augmentation. -/
theorem augT_freeRep (x : VHatCarrier W) (t : UEnv W ⊗[ℂ] M) : augT W M (freeRep W M x t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul e y =>
    change augT W M (freeEnd W M x (e ⊗ₜ[ℂ] y)) = 0
    rw [freeEnd_tmul, augT_tmul, leftReg_apply, map_mul, uAug_uι, zero_mul, zero_smul]
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]

theorem augT_freeRep_actMode (a : 𝒱) (m : ℤ) (t : UEnv W ⊗[ℂ] M) :
    augT W M ((freeRep W M).actMode a m t) = 0 := by
  rw [VHatRep.actMode_def]; exact augT_freeRep _ t

/-- The defect submodule lies in the kernel of the augmentation. -/
theorem defectSubmodule_le_ker_augT :
    VHatRep.defectSubmodule (freeRep W M) ≤ LinearMap.ker (augT W M) := by
  refine sInf_le ⟨?_, fun x d _ => augT_freeRep x d⟩
  rintro _ ⟨u, v, x, ℓ, N, rfl⟩
  rw [SetLike.mem_coe, VHatRep.defectVec]
  refine Submodule.sub_mem _ (augT_freeRep_actMode _ _ _) ?_
  set f : ℤ → UEnv W ⊗[ℂ] M := fun i => (negOnePow i * cbz ℓ i) •
    ((freeRep W M).actMode u (ℓ - i) ((freeRep W M).actMode v (N + i) x)
      - negOnePow ℓ • (freeRep W M).actMode v (ℓ + N - i) ((freeRep W M).actMode u i x))
  have hf : ∀ i, f i ∈ LinearMap.ker (augT W M) := fun i =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (augT_freeRep_actMode _ _ _)
      (Submodule.smul_mem _ _ (augT_freeRep_actMode _ _ _)))
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact Submodule.sum_mem _ fun i _ => hf i
  · rw [finsum_of_infinite_support hs]
    exact Submodule.zero_mem _

/-- The augmentation descended to `M̄(U)`. -/
noncomputable def augBar (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M] [Module ℂ M] :
    Mbar W M →ₗ[ℂ] M :=
  (VHatRep.defectSubmodule (freeRep W M)).liftQ (augT W M) defectSubmodule_le_ker_augT

theorem augBar_mk (t : UEnv W ⊗[ℂ] M) : augBar W M (Submodule.Quotient.mk t) = augT W M t := rfl

/-- `augBar` kills the image of every mode on `M̄(U)`. -/
theorem augBar_actMode (a : 𝒱) (m : ℤ) (x : Mbar W M) :
    augBar W M ((MbarRep W M).actMode a m x) = 0 := by
  refine Submodule.Quotient.induction_on _ x fun t => ?_
  rw [VHatRep.actMode_quotientRep, augBar_mk]
  exact augT_freeRep_actMode a m t

/-- `augBar [1 ⊗ y] = y`. -/
theorem augBar_one_tmul (y : M) : augBar W M (Submodule.Quotient.mk (1 ⊗ₜ[ℂ] y)) = y := by
  rw [augBar_mk, augT_tmul, map_one, one_smul]

/-! ## Vacuum normalisation forces a zero carrier -/

variable {MUcar : Type u} [AddCommGroup MUcar] [Module ℂ MUcar] {YMU : 𝒱 → ℤ → End ℂ MUcar}

/-- **A carrier bridge to a vacuum-normalised target forces `M = 0`.** -/
theorem CarrierBridge.subsingleton_of_vacuum (B : CarrierBridge W M MUcar YMU)
    (hvac : YMU W.vacuum (-1) = 1) : Subsingleton M := by
  have hid : ∀ x : Mbar W M, (MbarRep W M).actMode W.vacuum (-1) x = x := fun x =>
    B.equiv.injective (by rw [B.equivariant, hvac, Module.End.one_apply])
  refine ⟨fun y z => ?_⟩
  have h0 : ∀ y : M, y = 0 := fun y => by
    rw [← augBar_one_tmul (W := W) y, ← hid (Submodule.Quotient.mk (1 ⊗ₜ[ℂ] y)), augBar_actMode]
  rw [h0 y, h0 z]

theorem subsingleton_Mbar_of_subsingleton [Subsingleton M] : Subsingleton (Mbar W M) := by
  have h : ∀ t : UEnv W ⊗[ℂ] M, t = 0 := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul e y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
    | add t₁ t₂ h₁ h₂ => rw [h₁, h₂, add_zero]
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with | _ s => ?_
  induction y using Submodule.Quotient.induction_on with | _ t => ?_
  rw [h s, h t]

/-- The zero `A(𝒱)`-module: `AMod W` is never empty. -/
noncomputable def AMod.zero (W : VertexOperatorAlgebra 𝒱) : AMod W where
  carrier := PUnit
  ρ := 0
  ρ_one := Subsingleton.elim _ _
  ρ_mul _ _ := Subsingleton.elim _ _

instance (W : VertexOperatorAlgebra 𝒱) : Nonempty (AMod W) := ⟨AMod.zero W⟩

/-- **`CarrierBridgeFamily W` is uninhabited, for every `W`.** -/
theorem CarrierBridgeFamily.false (F : CarrierBridgeFamily W) : False := by
  let U := AMod.zero W
  have hv : F.YMU U W.vacuum (-1) = 1 := by rw [F.hvac]; simp
  haveI := (F.bridge U).subsingleton_of_vacuum hv
  haveI : Subsingleton (Mbar W U.carrier) := subsingleton_Mbar_of_subsingleton
  haveI : Subsingleton (MU W U) := (F.bridge U).equiv.symm.injective.subsingleton
  exact F.hbot U (Submodule.eq_bot_of_subsingleton)

instance (W : VertexOperatorAlgebra 𝒱) : IsEmpty (CarrierBridgeFamily W) := ⟨CarrierBridgeFamily.false⟩

/-- **`CarrierBridgeDataFamily W` is uninhabited, for every `W`.** -/
theorem CarrierBridgeDataFamily.false (F : CarrierBridgeDataFamily W) : False :=
  F.toCarrierBridgeFamily.false

instance (W : VertexOperatorAlgebra 𝒱) : IsEmpty (CarrierBridgeDataFamily W) :=
  ⟨CarrierBridgeDataFamily.false⟩

end VHat

end VOA

section AxiomAudit
#print axioms VOA.VHat.CarrierBridgeFamily.false
#print axioms VOA.VHat.CarrierBridgeDataFamily.false
end AxiomAudit

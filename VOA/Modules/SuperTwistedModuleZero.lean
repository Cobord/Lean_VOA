/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.SuperTwistedModule

/-!
# Every `SuperTwistedModule` with denominator `N ≥ 2` is the zero space

`SuperTwistedModule.jacobi` is quantified over every fractional label.  Instantiating it at
`u = w = 𝟙` (even, eigenvalue label `0`), `ℓ = -1`, `k = 1`, `m = -N-1` and using vacuum creation
(`vacuum_YM`) gives `x = 0` for every `x` as soon as `N ≥ 2`: the left side vanishes because no
index `-N·ℓ + 1 - iN` or `1 + iN` equals `-N` when `N ∤ 1`, while the right side is `x`.
In particular every parity-twisted ("Ramond") carrier `W.ParityTwistedModule M` is zero.

This was previously an out-of-library certificate (`Notes/Textbook/certificates/L17_Checks.lean`, §2);
it is recorded here so that the defect of the definition is visible in the library itself.
-/

open Module

namespace VOA

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperTwistedModule

/-- Vacuum creation in the `smul` API of a super vertex algebra: `𝟙₍ₙ₎ v = δ_{n,-1} v`. -/
theorem _root_.VOA.SuperVertexAlgebra.smul_vacuum_left (V : SuperVertexAlgebra 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul V.vacuum n v = if n = -1 then v else 0 := by
  rw [SuperVertexAlgebra.smul_def, V.vacuum_Y, mode_one]
  split_ifs <;> simp


theorem vacuum_mem_twistedEigenspace_zero {W : SuperVertexOperatorAlgebra 𝒱}
    (g : SuperAut W) (N : ℕ) : W.vacuum ∈ g.twistedEigenspace N 0 := by
  rw [SuperAut.twistedEigenspace, Module.End.mem_eigenspace_iff]
  change g.toLinearEquiv W.vacuum = _
  rw [g.map_vacuum]
  simp

private theorem ne_neg_of_two_le {N : ℕ} (hN : 2 ≤ N) (i : ℤ) :
    (-1) * (N : ℤ) + 1 - i * N ≠ -(N : ℤ) ∧ 1 + i * (N : ℤ) ≠ -(N : ℤ) := by
  have hdvd : ∀ c : ℤ, c * (N : ℤ) = 1 ∨ c * (N : ℤ) = -1 → False := by
    intro c hc
    have h1 : (N : ℤ) ∣ 1 := by
      rcases hc with hc | hc
      · exact ⟨c, by rw [← hc]; ring⟩
      · exact ⟨-c, by linear_combination hc⟩
    have := Int.le_of_dvd one_pos h1
    omega
  refine ⟨fun h => hdvd i (Or.inl (by linear_combination -h)), fun h =>
    hdvd (i + 1) (Or.inr (by linear_combination h))⟩

/-- **Every `SuperTwistedModule` with denominator `N ≥ 2` is the zero space.**
Instance of `jacobi`: `u = w = 𝟙` (even, `j = 0`), `ℓ = -1`, `k = 1`, `m = -N-1`. -/
theorem superTwistedModule_eq_zero {W : SuperVertexOperatorAlgebra 𝒱} {g : SuperAut W}
    {N : ℕ} (hN : 2 ≤ N) {M : Type v} [AddCommGroup M] [Module ℂ M]
    (T : SuperTwistedModule W g N M) (x : M) : x = 0 := by
  have h := T.jacobi (p := 0) (q := 0) 0 W.vacuum (vacuum_mem_twistedEigenspace_zero g N)
    W.vacuum_parity W.vacuum W.vacuum_parity x (-1) 1 (-(N : ℤ) - 1)
  have hvac := T.vacuum_YM
  have hL : (∑ᶠ i : ℤ, (negOnePow i * cbz (-1) i) •
      (T.YM W.vacuum ((-1) * N + 1 - i * N) (T.YM W.vacuum ((-(N : ℤ) - 1) + i * N) x)
        - (koszul 0 0 * negOnePow (-1)) • T.YM W.vacuum ((-1) * N + (-(N : ℤ) - 1) - i * N)
            (T.YM W.vacuum (1 + i * N) x))) = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
    obtain ⟨h1, h2⟩ := ne_neg_of_two_le hN i
    simp only [hvac, if_neg h1, if_neg h2]
    simp
  have hR : (∑ᶠ i : ℕ, fractionalBinom ((1 : ℤ) / (N : ℂ)) i •
      T.YM (W.smul W.vacuum (-1 + i) W.vacuum) (1 + (-(N : ℤ) - 1) - i * N) x) = x := by
    rw [finsum_eq_single _ 0 (fun i hi => by
      rw [SuperVertexAlgebra.smul_vacuum_left, if_neg (by omega), map_zero]
      simp)]
    rw [SuperVertexAlgebra.smul_vacuum_left, if_pos (by simp)]
    simp only [fractionalBinom, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
      Nat.cast_one, div_one, one_smul]
    rw [hvac, if_pos (by push_cast; ring)]
    rfl
  rw [hL, hR] at h
  exact h.symm

/-- Hence the carrier is a subsingleton and every weight space is `⊥`. -/
theorem superTwistedModule_subsingleton {W : SuperVertexOperatorAlgebra 𝒱} {g : SuperAut W}
    {N : ℕ} (hN : 2 ≤ N) {M : Type v} [AddCommGroup M] [Module ℂ M]
    (T : SuperTwistedModule W g N M) : Subsingleton M :=
  ⟨fun x y => by rw [superTwistedModule_eq_zero hN T x, superTwistedModule_eq_zero hN T y]⟩

theorem superTwistedModule_weight_eq_bot {W : SuperVertexOperatorAlgebra 𝒱} {g : SuperAut W}
    {N : ℕ} (hN : 2 ≤ N) {M : Type v} [AddCommGroup M] [Module ℂ M]
    (T : SuperTwistedModule W g N M) (α : ℂ) : T.weight α = ⊥ := by
  rw [eq_bot_iff]
  intro x _
  rw [superTwistedModule_eq_zero hN T x]
  exact Submodule.zero_mem _

/-- In particular every parity-twisted ("Ramond") carrier is zero. -/
theorem parityTwistedModule_eq_zero {W : SuperVertexOperatorAlgebra 𝒱} {M : Type v}
    [AddCommGroup M] [Module ℂ M] (T : W.ParityTwistedModule M) (x : M) : x = 0 :=
  superTwistedModule_eq_zero (le_refl 2) T x

end SuperTwistedModule

end VOA

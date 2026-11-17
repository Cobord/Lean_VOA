/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.Fusion

/-!
# `fusionCoeff` is identically zero

`VOA.fusionCoeff A B C` (VOA/Modules/Fusion.lean) is `Module.finrank ℂ (IntertwinerSpace A B C)`.
We prove it is identically `0`: the intertwiner space is either `⊥` or infinite-dimensional,
and Mathlib's `finrank` of an infinite-dimensional space is `0` by convention.

The infinite family: if `Y ≠ 0` in the space, pick `s₀, u, x` with `Y s₀ u x ≠ 0`; for each
`k : ℕ` restrict `Y` to the coset `s₀ + ℤ` and shift it by `c_k = I·k`.  The defining
"intertwining defect" condition only relates `Y_s` to `Y_{s+p-j}` (same coset, coefficients
independent of `s`), so each shifted restriction lies in the space; evaluation at `s₀ + I·k`
separates them, so they are linearly independent.

So `fusionCoeff` does not compute fusion rules; it is recorded here (previously an out-of-library
certificate, `Notes/Textbook/certificates/L12_FusionCoeffZero.lean`) so that the defect of the
definition is visible in the library itself.
-/

open Classical

universe u

namespace VOA.FusionCoeffZero

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M N P : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  [AddCommGroup P] [Module ℂ P]

/-- Restrict `Y` to the coset `s₀ + c + ℤ` after shifting the exponent by `c`. -/
noncomputable def shiftRestrict (Y : IntertwinerModes M N P) (s₀ c : ℂ) :
    IntertwinerModes M N P :=
  fun s => if (∃ n : ℤ, s = s₀ + c + n) then Y (s - c) else 0

theorem coset_shift {s s₀ c : ℂ} (p : ℤ) (j : ℕ) :
    (∃ n : ℤ, s + p - j = s₀ + c + n) ↔ (∃ n : ℤ, s = s₀ + c + n) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n - p + j, by push_cast; linear_combination hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + p - j, by push_cast; linear_combination hn⟩

theorem shiftRestrict_mem (A : OrdVModule W M) (B : OrdVModule W N) (C : OrdVModule W P)
    {Y : IntertwinerModes M N P} (hY : Y ∈ IntertwinerSpace A B C) (s₀ c : ℂ) :
    shiftRestrict Y s₀ c ∈ IntertwinerSpace A B C := by
  have hY0 : intertwiningDefect A B C Y = 0 := hY
  show intertwiningDefect A B C (shiftRestrict Y s₀ c) = 0
  funext a p s u x
  have hYs := congrFun (congrFun (congrFun (congrFun (congrFun hY0 a) p) (s - c)) u) x
  simp only [intertwiningDefect, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hYs ⊢
  by_cases hs : ∃ n : ℤ, s = s₀ + c + n
  · have hsum : (∑ᶠ j : ℕ, intertwinerSummand A (shiftRestrict Y s₀ c) a p s u x j)
        = ∑ᶠ j : ℕ, intertwinerSummand A Y a p (s - c) u x j := by
      refine finsum_congr (fun j => ?_)
      simp only [intertwinerSummand, shiftRestrict]
      rw [if_pos ((coset_shift p j).mpr hs)]
      congr 3
      ring_nf
    rw [hsum]
    simp only [shiftRestrict, if_pos hs]
    exact hYs
  · have hsum : (∑ᶠ j : ℕ, intertwinerSummand A (shiftRestrict Y s₀ c) a p s u x j) = 0 := by
      rw [← finsum_zero (α := ℕ)]
      refine finsum_congr (fun j => ?_)
      simp only [intertwinerSummand, shiftRestrict]
      rw [if_neg (fun h => hs ((coset_shift p j).mp h))]
      simp
    rw [hsum]
    simp only [shiftRestrict, if_neg hs]
    simp

/-- The key evaluation: `shiftRestrict Y s₀ (I*l)` at `s₀ + I*k` is `Y s₀` if `k = l`, else `0`. -/
theorem shiftRestrict_eval (Y : IntertwinerModes M N P) (s₀ : ℂ) (k l : ℕ) :
    shiftRestrict Y s₀ (Complex.I * l) (s₀ + Complex.I * k)
      = if k = l then Y s₀ else 0 := by
  unfold shiftRestrict
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos ⟨0, by simp⟩, if_pos rfl]
    congr 1; ring_nf
  · rw [if_neg hkl, if_neg]
    rintro ⟨n, hn⟩
    have him := congrArg Complex.im hn
    simp at him
    exact hkl (by exact_mod_cast him)

theorem not_finite_of_ne_zero (A : OrdVModule W M) (B : OrdVModule W N) (C : OrdVModule W P)
    {Y : IntertwinerModes M N P} (hY : Y ∈ IntertwinerSpace A B C) (hne : Y ≠ 0) :
    ¬ Module.Finite ℂ (IntertwinerSpace A B C) := by
  -- a nonzero value `Y s₀ u x`
  obtain ⟨s₀, u, x, hval⟩ : ∃ s₀ u x, Y s₀ u x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext fun s => LinearMap.ext fun u => LinearMap.ext fun x => h s u x)
  intro hfin
  let f : ℕ → IntertwinerSpace A B C := fun k =>
    ⟨shiftRestrict Y s₀ (Complex.I * k), shiftRestrict_mem A B C hY s₀ _⟩
  have hli : LinearIndependent ℂ f := by
    apply LinearIndependent.of_comp (IntertwinerSpace A B C).subtype
    rw [linearIndependent_iff']
    intro t g hsum i hi
    have h := congrArg (fun Z : IntertwinerModes M N P => Z (s₀ + Complex.I * i) u x) hsum
    simp only [Function.comp_apply, Submodule.subtype_apply, f] at h
    rw [Finset.sum_apply] at h
    simp only [Pi.smul_apply, shiftRestrict_eval, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply] at h
    rw [Finset.sum_eq_single i] at h
    · have h' : g i • Y s₀ u x = 0 := by simpa using h
      exact (smul_eq_zero.mp h').resolve_right hval
    · intro j _ hji
      rw [if_neg (Ne.symm hji)]
      simp
    · intro hin; exact absurd hi hin
  haveI := hli.finite
  exact not_finite ℕ

/-- **`fusionCoeff` is identically zero.** -/
theorem fusionCoeff_eq_zero (A : OrdVModule W M) (B : OrdVModule W N) (C : OrdVModule W P) :
    fusionCoeff A B C = 0 := by
  unfold fusionCoeff
  by_cases h : ∃ Y ∈ IntertwinerSpace A B C, Y ≠ 0
  · obtain ⟨Y, hY, hne⟩ := h
    exact Module.finrank_of_not_finite (not_finite_of_ne_zero A B C hY hne)
  · push Not at h
    have hbot : IntertwinerSpace A B C = ⊥ := (Submodule.eq_bot_iff _).mpr h
    rw [hbot]
    exact finrank_bot ℂ _

end VOA.FusionCoeffZero

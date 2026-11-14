import VOA.Moonshine.MoonshineCNLattice
import VOA.Examples.HeisenbergNFock

/-!
# Heisenberg oscillators for the hyperbolic plane

A complex bilinear coordinate map replaces the positive-definite real frame.
There is no conjugation in its pairing identity.
-/

namespace VOA.Moonshine.ConwayNorton

open HeisenbergN
open scoped BigOperators

/-- Fock oscillators associated to an arbitrary complex coordinate vector. -/
noncomputable def complexChargeOscillator {r : ℕ} (v : Fin r → ℂ) (m : ℤ) :
    Module.End ℂ (FockN r) := ∑ a, v a • oscN r 1 a m

theorem complexChargeOscillator_vacuum {r : ℕ} (v : Fin r → ℂ) (m : ℤ)
    (hm : 0 ≤ m) : complexChargeOscillator v m (vacuumN r) = 0 := by
  simp [complexChargeOscillator, oscN_vacuum r 1 _ m hm]

/-- The oscillator commutator uses the complex bilinear dot product. -/
theorem complexChargeOscillator_commutator {r : ℕ} (v w : Fin r → ℂ) (m n : ℤ) :
    ⁅complexChargeOscillator v m, complexChargeOscillator w n⁆ =
      (if m + n = 0 then (∑ a, v a * w a) * (m : ℂ) else 0) • LinearMap.id := by
  simp only [complexChargeOscillator, Ring.lie_def]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun b a => (w b • oscN r 1 b n) * (v a • oscN r 1 a m)), ← Finset.sum_sub_distrib]
  have key : ∀ a b : Fin r,
      (v a • oscN r 1 a m) * (w b • oscN r 1 b n) - (w b • oscN r 1 b n) * (v a • oscN r 1 a m)
        = (v a * w b) • (if a = b ∧ m + n = 0 then (m : ℂ) * 1 else 0) • LinearMap.id := by
    intro a b
    rw [← oscN_comm, smul_sub, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (w b)]
  simp only [← Finset.sum_sub_distrib, key, smul_smul, mul_one]
  by_cases h : m + n = 0
  · simp only [h, and_true, mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, ← Finset.sum_smul, ← Finset.sum_mul]
  · simp [h]

/-- An explicit complex frame: `(x+y/2, i(x-y/2))` has bilinear norm `2xy`. -/
noncomputable def complexHyperbolicCoordinate (x : lorentzianLattice.carrier) : Fin 2 → ℂ :=
  ![(x 0 : ℂ) + (x 1 : ℂ) / 2, Complex.I * ((x 0 : ℂ) - (x 1 : ℂ) / 2)]

theorem complexHyperbolicCoordinate_pairing (x y : lorentzianLattice.carrier) :
    (∑ a, complexHyperbolicCoordinate x a * complexHyperbolicCoordinate y a) =
      (lorentzianLattice.form x y : ℂ) := by
  simp only [complexHyperbolicCoordinate, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, lorentzian_form_apply]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The hyperbolic-plane Heisenberg action on the rank-two Fock space. -/
noncomputable def lorentzianOscillator (x : lorentzianLattice.carrier) (m : ℤ) :
    Module.End ℂ (FockN 2) := complexChargeOscillator (complexHyperbolicCoordinate x) m

theorem lorentzianOscillator_commutator (x y : lorentzianLattice.carrier) (m n : ℤ) :
    ⁅lorentzianOscillator x m, lorentzianOscillator y n⁆ =
      (if m + n = 0 then (lorentzianLattice.form x y : ℂ) * (m : ℂ) else 0) •
        LinearMap.id := by
  rw [lorentzianOscillator, lorentzianOscillator, complexChargeOscillator_commutator,
    complexHyperbolicCoordinate_pairing]

theorem lorentzianOscillator_vacuum (x : lorentzianLattice.carrier) (m : ℤ)
    (hm : 0 ≤ m) : lorentzianOscillator x m (vacuumN 2) = 0 :=
  complexChargeOscillator_vacuum (complexHyperbolicCoordinate x) m hm

end VOA.Moonshine.ConwayNorton

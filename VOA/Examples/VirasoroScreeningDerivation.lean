/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningMoment
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Finite Laurent differentiation for screening Ward identities

Euler differentiation multiplies a Laurent coefficient by its integer exponent.
Multiplication by a monomial shifts this to the vector field z^(n+1) d/dz.
The coefficient formula is the finite algebraic integration-by-parts rule;
negative exponents are retained as integers, never truncated natural differences.
-/
namespace VOA.VirasoroScreening
open scoped BigOperators
open AddMonoidAlgebra

/-- Euler differentiation in one auxiliary variable, on finite Laurent expressions. -/
noncomputable def laurentEuler {r : ℕ} (i : Fin r) :
    Laurent (Fin r → ℤ) →ₗ[ℚ] Laurent (Fin r → ℤ) :=
  (Finsupp.lsum ℚ (fun e : Fin r → ℤ => (e i : ℚ) • AddMonoidAlgebra.lsingle (R := ℚ) e)) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

/-- A Laurent monomial is an Euler eigenvector with its signed integer exponent. -/
theorem laurentEuler_single {r : ℕ} (i : Fin r) (e : Fin r → ℤ) (q : ℚ) :
    laurentEuler i (single e q) = single e ((e i : ℚ)*q) := by
  change (Finsupp.lsum ℚ (fun e : Fin r → ℤ => (e i : ℚ) • AddMonoidAlgebra.lsingle (R := ℚ) e))
    (Finsupp.single e q) = _
  rw [Finsupp.lsum_single, LinearMap.smul_apply, AddMonoidAlgebra.lsingle_apply,
    AddMonoidAlgebra.smul_single']

/-- Euler differentiation acts coefficient by coefficient, including negative exponents. -/
theorem laurentEuler_apply {r : ℕ} (i : Fin r) (P : Laurent (Fin r → ℤ))
    (e : Fin r → ℤ) : (laurentEuler i P).coeff e = (e i : ℚ)*P.coeff e := by
  classical
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ =>
    rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hP, hQ, mul_add]
  | single a q =>
    rw [laurentEuler_single, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single]
    by_cases h : a = e
    · subst a; simp
    · simp [Finsupp.single_apply, h]

/-- Euler differentiation satisfies the product rule in the actual Laurent algebra. -/
theorem laurentEuler_mul {r : ℕ} (i : Fin r) (P Q : Laurent (Fin r → ℤ)) :
    laurentEuler i (P*Q) = laurentEuler i P*Q + P*laurentEuler i Q := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P R hP hR => simp only [add_mul, map_add, hP, hR]; abel
  | single a p =>
    induction Q using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add Q R hQ hR => simp only [mul_add, map_add, hQ, hR]; abel
    | single b q =>
      simp only [single_mul_single, laurentEuler_single, Pi.add_apply, Int.cast_add,
        ← single_add]
      congr 1
      ring

/-- The sum of the auxiliary vector fields z_i^(n+1) d/dz_i, defined for
any integer n without division or an infinite Laurent expansion. -/
noncomputable def screeningVectorField (r : ℕ) (n : ℤ) :
    Laurent (Fin r → ℤ) →ₗ[ℚ] Laurent (Fin r → ℤ) :=
  ∑ i : Fin r, (LinearMap.mulLeft ℚ (single (n • unitExponent r i) 1)).comp
    (laurentEuler i)

/-- The finite vector field obeys the product rule. -/
theorem screeningVectorField_mul (r : ℕ) (n : ℤ) (P Q : Laurent (Fin r → ℤ)) :
    screeningVectorField r n (P*Q) =
      screeningVectorField r n P*Q + P*screeningVectorField r n Q := by
  simp only [screeningVectorField, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, laurentEuler_mul, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- Exact coefficient integration by parts: the coefficient at exponent e
uses e_i-n at the shifted exponent. The subtraction is genuinely integral. -/
theorem screeningVectorField_apply (r : ℕ) (n : ℤ) (P : Laurent (Fin r → ℤ))
    (e : Fin r → ℤ) :
    (screeningVectorField r n P).coeff e =
      ∑ i : Fin r, ((e i - n : ℤ) : ℚ) * P.coeff (e - n • unitExponent r i) := by
  classical
  simp only [screeningVectorField, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply]
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, laurentEuler_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp [unitExponent, sub_eq_add_neg, add_comm]

end VOA.VirasoroScreening

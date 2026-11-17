import VOA.Classification.COne.OrbIcoVVacFlat

/-! Coefficient continuity of the actual positive Virasoro equations in
fixed Fock columns. The oscillator operators are fixed; only their scalar
background and momentum coefficients vary. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.SparseRational VOA.VirasoroScreening
  InverseDS.VirasoroVerma InverseDS.LeeYangFockVirasoro Filter Topology

theorem fockRawEval_end_coeff_continuousAt (A : Module.End ℂ FF)
    (s₀ : ℂ) (hs : s₀ ≠ 0) (P : RawPoly ℕ) (d : (ℕ × Fin 1) →₀ ℕ) :
    ContinuousAt (fun s => (A (fockRawEval s P)).coeff d) s₀ := by
  induction P with
  | nil => simpa [fockRawEval,evalRaw] using! (continuousAt_const :
      ContinuousAt (fun _ : ℂ => (0 : ℂ)) s₀)
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    have he (s : ℂ) : (A (fockRawEval s ((q,w)::P))).coeff d =
        (q:ℂ)*fockWordScalar s w*(A (evalWord fockBaseVar w)).coeff d +
          (A (fockRawEval s P)).coeff d := by
      change (A (algebraMap ℚ FF q*evalWord (fockRawVar s) w+
        fockRawEval s P)).coeff d = _
      rw [fock_rat_mul,fockWord_scalar,map_add,map_smul,map_smul,
        AddMonoidAlgebra.coeff_add,Finsupp.add_apply,coeff_smul,coeff_smul]
      simp only [smul_eq_mul]
      ring
    simp_rw [he]
    exact ((continuousAt_const.mul (fockWordScalar_continuousAt s₀ hs w)).mul
      continuousAt_const).add ih

theorem sector_mode_coefficient_continuousAt (ell p : ℂ → ℂ)
    (s₀ : ℂ) (hs : s₀ ≠ 0) (he : ContinuousAt ell s₀) (hp : ContinuousAt p s₀)
    (m : ℤ) (hm : m ≠ 0) (P : RawPoly ℕ) (d : (ℕ × Fin 1) →₀ ℕ) :
    ContinuousAt (fun s => (sectorVirasoro (ell s) (p s) m
      (fockRawEval s P)).coeff d) s₀ := by
  have hf (s : ℂ) : (sectorVirasoro (ell s) (p s) m (fockRawEval s P)).coeff d =
      (LvirN 1 2 m (fockRawEval s P)).coeff d+
        p s*(alphaMode m (fockRawEval s P)).coeff d-
        ((m:ℂ)+1)*ell s*(alphaMode m (fockRawEval s P)).coeff d := by
    simp only [sectorVirasoro,sectorSugawara,sectorBackgroundCurrent,sectorCurrent,
      if_neg hm,zero_smul,add_zero,LinearMap.sub_apply,LinearMap.add_apply,
      LinearMap.smul_apply,coeff_sub,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,coeff_smul,
      smul_eq_mul]
    ring
  simp_rw [hf]
  exact ((fockRawEval_end_coeff_continuousAt _ s₀ hs P d).add
    (hp.mul (fockRawEval_end_coeff_continuousAt _ s₀ hs P d))).sub
    ((continuousAt_const.mul he).mul (fockRawEval_end_coeff_continuousAt _ s₀ hs P d))

theorem familyBackground_continuousAt (s₀ : ℂ) (hs : s₀ ≠ 0) :
    ContinuousAt familyBackground s₀ :=
  (continuousAt_id.sub (continuousAt_id.inv₀ hs)).div_const 2

theorem familyMomentum_continuousAt (s₀ : ℂ) (hs : s₀ ≠ 0) :
    ContinuousAt familyMomentum s₀ :=
  continuousAt_const.div continuousAt_id hs

end VOA.Classification.COne.OrbIcoV

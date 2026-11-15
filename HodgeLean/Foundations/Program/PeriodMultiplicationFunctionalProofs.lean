import HodgeLean.Foundations.Program.PeriodMultiplicationHarmonicProofs

noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b3Forms_isManifold_real
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

variable (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
  {U : Set (Fin 10 → ℂ)}
  (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)

/-- The original flat period functional extended to complex homology. -/
def b66m_flatPeriod :
    (ℂ ⊗[ℤ] b66g_Homology R s) →ₗ[ℂ] ((Fin 10 → ℂ) → ℂ) :=
  LinearMap.liftBaseChange ℂ
    (b63e_periodFunctionLinear mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) R.P θ s)

/-- Pure tensors evaluate to the corresponding original fixed-cycle period function. -/
theorem b66m_flatPeriod_tmul (c : ℂ) (x : b66g_Homology R s) :
    b66m_flatPeriod R s θ (c ⊗ₜ[ℤ] x) =
      c • b63e_periodFunction mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) R.P θ s x := by
  rw [b66m_flatPeriod, LinearMap.liftBaseChange_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Complexified original flat periods are analytic on the relative form's domain. -/
theorem b66m_flatPeriod_analytic (hU : IsOpen U) (x : ℂ ⊗[ℤ] b66g_Homology R s) :
    AnalyticOnNhd ℂ (b66m_flatPeriod R s θ x) (b6t_polydisc mr_base ∩ U) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    exact analyticOnNhd_const
  | add x y hx hy =>
    rw [map_add]
    exact hx.add hy
  | tmul c x =>
    rw [b66m_flatPeriod_tmul]
    apply AnalyticOnNhd.const_smul
    exact b63e_period_analytic mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
      (rf5_polydisc_isOpen mr_base)
      (fun p => ⟨R.atlas.A p, (R.atlas.hA p).2, (R.atlas.hA p).1, R.atlas.hparam p⟩)
      R.hincl R.P R.hP U hU θ s x

/-- Flat integral homology transported to the full period lattice. -/
def b66m_fullTransport (t : b6t_polydisc mr_base) :
    b66g_Homology R s →ₗ[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t) :=
  (R.P t).comp (b6m_H1Equiv (b6m_transport mr_base R.C s t)).toIntLinearEquiv.toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the flat functional is evaluation of the transported full lattice period. -/
theorem b66m_flatPeriod_transport (t : b6t_polydisc mr_base)
    (x : ℂ ⊗[ℤ] b66g_Homology R s) :
    b66m_flatPeriod R s θ x t.val =
      b3_cplxPeriod ℂ (rf8_fibre R.C t) ((b66m_fullTransport R s t).baseChange ℂ x)
        (b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) θ t) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul c x =>
    rw [b66m_flatPeriod_tmul, LinearMap.baseChange_tmul]
    simp only [Pi.smul_apply, smul_eq_mul, b63e_periodFunction,
      dite_eq_left t.property, b3_cplxPeriod, LinearMap.liftBaseChange_tmul]
    rfl

section Derivative
variable (t : b6t_polydisc mr_base)
    (q : b66g_Coeff R) (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66g_forms R t 1)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic harmonic functional is the derivative on complexified original homology. -/
theorem b66m_complexPeriodFunctional_flat (x : ℂ ⊗[ℤ] b66g_Homology R s) :
    b66m_complexPeriodFunctional R t
      (b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.reCLM)
      (b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.imCLM)
      ((b66m_fullTransport R s t).baseChange ℂ x) =
      fderiv ℂ (b66m_flatPeriod R s θ x) t.val h := by
  have hd (x : ℂ ⊗[ℤ] b66g_Homology R s) :
      DifferentiableAt ℂ (b66m_flatPeriod R s θ x) t.val :=
    (b66m_flatPeriod_analytic R s θ hU x t.val ⟨t.property, ht⟩).differentiableAt
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, fderiv_zero, Pi.zero_apply, ContinuousLinearMap.zero_apply]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, fderiv_add (hd x) (hd y)]
    rfl
  | tmul c x =>
    rw [LinearMap.baseChange_tmul, b66m_complexPeriodFunctional_tmul,
      b66m_flatPeriod_tmul]
    change c * ((b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.reCLM
        (b3Rest2_θ (Module.finrank_self ℂ)
          (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) x))) : ℂ) +
      Complex.I * (b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.imCLM
        (b3Rest2_θ (Module.finrank_self ℂ)
          (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) x))) : ℂ)) = _
    rw [b66m_correctedParameterHolPairing_flat R t θ q h ρ hU ht hqf hq hρ,
      b66m_correctedParameterHolPairing_flat R t θ q h ρ hU ht hqf hq hρ]
    simp only [Complex.reCLM_apply, Complex.imCLM_apply, mul_comm Complex.I, Complex.re_add_im]
    have hd' : DifferentiableAt ℂ
        (b63e_periodFunction mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) R.P θ s x) t.val := by
      simpa only [b66m_flatPeriod_tmul, one_smul] using hd (1 ⊗ₜ[ℤ] x)
    rw [fderiv_const_smul hd']
    rfl

end Derivative

/-- Differentiating a vanishing moving graph functional removes the moving coefficients. -/
theorem b66m_movingFunctional_derivative {V : Type*} [AddCommGroup V] [Module ℂ V]
    {κ : Type*} [Fintype κ]
    (P : V →ₗ[ℂ] ((Fin 10 → ℂ) → ℂ)) (v₀ : V) (v : κ → V)
    (z : (Fin 10 → ℂ) → κ → ℂ) (t h : Fin 10 → ℂ)
    (hP₀ : DifferentiableAt ℂ (P v₀) t)
    (hP : ∀ k, DifferentiableAt ℂ (P (v k)) t)
    (hz : ∀ k, DifferentiableAt ℂ (fun u => z u k) t)
    (hzero : ∀ᶠ u in 𝓝 t, P (v₀ + ∑ k, z u k • v k) u = 0) :
    fderiv ℂ (P (v₀ + ∑ k, z t k • v k)) t h =
      -∑ k, fderiv ℂ (fun u => z u k) t h * P (v k) t := by
  classical
  let f := fun u => P v₀ u + ∑ k, z u k * P (v k) u
  have he : f =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [hzero] with u hu
    simpa only [map_add, map_sum, map_smul, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, f] using hu
  have hd := hP₀.hasFDerivAt.add
    (HasFDerivAt.sum (u := Finset.univ) (fun k _ => (hz k).hasFDerivAt.mul (hP k).hasFDerivAt))
  have hfun : (P v₀ + ∑ i, (fun u => z u i) * P (v i)) = f := by
    funext u
    simp only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, f]
  rw [hfun] at hd
  have hdf : fderiv ℂ f t = 0 := by
    rw [he.fderiv_eq]
    exact (hasFDerivAt_const (c := (0 : ℂ)) t).fderiv
  have heval := congrArg (fun L : (Fin 10 → ℂ) →L[ℂ] ℂ => L h)
    (hd.fderiv.symm.trans hdf)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply] at heval
  have hfixed : fderiv ℂ (P (v₀ + ∑ k, z t k • v k)) t h =
      fderiv ℂ (P v₀) t h + ∑ k, z t k * fderiv ℂ (P (v k)) t h := by
    simp only [map_add, map_sum, map_smul]
    rw [fderiv_add hP₀ (DifferentiableAt.sum (fun k _ => (hP k).const_smul (z t k))),
      fderiv_sum (fun k _ => (hP k).const_smul (z t k))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      fderiv_const_smul (hP _), ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hfixed]
  rw [Finset.sum_add_distrib] at heval
  have hcomm : (∑ k, P (v k) t * fderiv ℂ (fun u => z u k) t h) =
      ∑ k, fderiv ℂ (fun u => z u k) t h * P (v k) t :=
    Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  rw [hcomm] at heval
  linear_combination heval

/-- The positive graph frame gives the transpose order in the flat functional derivative. -/
theorem b66m_positive_frame_derivative
    (P : (ℂ ⊗[ℤ] b60_Lattice) →ₗ[ℂ] ((Fin 10 → ℂ) → ℂ))
    (z : (Fin 10 → ℂ) → Fin 9 → ℂ) (t h : Fin 10 → ℂ) (j : Fin 3)
    (hP : ∀ n, DifferentiableAt ℂ (P n) t)
    (hz : DifferentiableAt ℂ z t)
    (hzero : ∀ᶠ u in 𝓝 t, P (b60_frame (z u) (1, j)) u = 0) :
    fderiv ℂ (P (b60_frame (z t) (1, j))) t h =
      -∑ k : Fin 3, (fderiv ℂ z t h) (finProdFinEquiv (j, k)) *
        P (b60_eigen 1 (Fin.castAdd 3 k)) t := by
  have hd := b66m_movingFunctional_derivative P
    (b60_eigen 1 (Fin.natAdd 3 j)) (fun k : Fin 3 => b60_eigen 1 (Fin.castAdd 3 k))
    (fun u k => g32m_toMat (z u) j k) t h (hP _) (fun k => hP _)
    (fun k => differentiableAt_pi.mp hz (finProdFinEquiv (j, k)))
    (by simpa only [b60_frame, show (1 : Fin 2) ≠ 0 by decide, ite_eq_right, ite_false] using hzero)
  simpa only [b60_frame, show (1 : Fin 2) ≠ 0 by decide, ite_eq_right, ite_false, g32m_toMat, Matrix.of_apply,
    fderiv_apply hz, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using hd

end HodgeLean.Foundations.Program

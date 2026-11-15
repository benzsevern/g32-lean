import HodgeLean.Foundations.Program.PeriodMultiplicationDeRhamProofs

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b3Forms_isManifold_real
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

variable (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℤ (b3_periodLattice ℂ (rf8_fibre R.C t)))

set_option maxHeartbeats 400000 in
/-- The original intersection pairing in one integral and one complexified lattice variable. -/
theorem b66m_intersection_right_coords (l : b3_periodLattice ℂ (rf8_fibre R.C t))
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t)) :
    (R.Q t).baseChange ℂ (1 ⊗ₜ[ℤ] l) y =
      (b3Rest2_W (Module.finrank_self ℂ) (b3Rest2_θ (Module.finrank_self ℂ) l)
        (b3Rest2_uR (Module.finrank_self ℂ) b ((Algebra.TensorProduct.basis ℂ b).equivFun y)) : ℂ) +
      Complex.I * (b3Rest2_W (Module.finrank_self ℂ) (b3Rest2_θ (Module.finrank_self ℂ) l)
        (b3Rest2_uI (Module.finrank_self ℂ) b ((Algebra.TensorProduct.basis ℂ b).equivFun y)) : ℂ) := by
  let B := Algebra.TensorProduct.basis ℂ b
  have he : (R.Q t).baseChange ℂ (1 ⊗ₜ[ℤ] l) y =
      ∑ i, B.equivFun y i * (R.Q t l (b i) : ℂ) := by
    conv_lhs => rw [← B.sum_equivFun y]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, b3Rest2_tmulBasis (Module.finrank_self ℂ) b,
      LinearMap.BilinForm.baseChange_tmul]
    simp only [one_mul, zsmul_eq_mul, mul_one, smul_eq_mul]
  rw [he]
  simp only [b3Rest2_uR, b3Rest2_uI, map_sum, map_smul, smul_eq_mul,
    Complex.ofReal_sum]
  conv_rhs => rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hQ := congrArg (fun r : ℝ => (r : ℂ)) (b66m_intersection_lattice_W R t l (b i))
  simp only [Complex.ofReal_intCast] at hQ
  rw [hQ]
  change B.equivFun y i * _ = _
  dsimp only [B]
  apply Complex.ext <;> simp <;> ring

/-- The holomorphic form specified by polarization on a vector of the full Hodge filtration. -/
def b66m_polarizedHarmonicForm
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t)) :
    b3_HolForm ℂ (rf8_fibre R.C t) :=
  -b3Rest2_uR (Module.finrank_self ℂ) b ((Algebra.TensorProduct.basis ℂ b).equivFun y)

/-- Full lattice periods of this form use the original supplied intersection pairing. -/
theorem b66m_polarizedHarmonicForm_period
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t))
    (hy : y ∈ b3_periodF ℂ (rf8_fibre R.C t))
    (l : b3_periodLattice ℂ (rf8_fibre R.C t)) :
    l.val (b66m_polarizedHarmonicForm R t b y) = (R.Q t).baseChange ℂ (1 ⊗ₜ[ℤ] l) y := by
  rw [b66m_intersection_right_coords R t b,
    b3Rest2_uI_of_mem_F (Module.finrank_self ℂ) b hy]
  rw [b3Rest2_lattice_apply (Module.finrank_self ℂ)]
  simp only [b66m_polarizedHarmonicForm, map_neg, LinearMap.neg_apply,
    smul_neg, neg_smul]
  let u := b3Rest2_uR (Module.finrank_self ℂ) b ((Algebra.TensorProduct.basis ℂ b).equivFun y)
  rw [b3Rest2_W_skew (Module.finrank_self ℂ) u (b3Rest2_θ (Module.finrank_self ℂ) l),
    b3Rest2_W_skew (Module.finrank_self ℂ) (Complex.I • u) (b3Rest2_θ (Module.finrank_self ℂ) l)]
  push_cast
  ring


/-- Complex coefficients acting on two real period components. -/
theorem b66m_complex_real_period_sum (c : ι → ℂ) (a d : ι → ℝ) :
    ∑ i, c i * ((a i : ℂ) + Complex.I * (d i : ℂ)) =
      ((∑ i, (c i).re * a i - ∑ i, (c i).im * d i : ℝ) : ℂ) +
      Complex.I * ((∑ i, (c i).re * d i + ∑ i, (c i).im * a i : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- The four real trace pairings are evaluation of the complexified period functional. -/
theorem b66m_polarizedHarmonicForm_functional
    (A D : b3_HolForm ℂ (rf8_fibre R.C t) →ₗ[ℝ] ℝ)
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t))
    (hy : y ∈ b3_periodF ℂ (rf8_fibre R.C t)) :
    -(A (b66m_polarizedHarmonicForm R t b y) : ℂ) -
      (D (Complex.I • b66m_polarizedHarmonicForm R t b y) : ℂ) +
      Complex.I * ((A (Complex.I • b66m_polarizedHarmonicForm R t b y) : ℂ) -
        (D (b66m_polarizedHarmonicForm R t b y) : ℂ)) =
      ∑ i, (Algebra.TensorProduct.basis ℂ b).equivFun y i *
        ((A (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ) +
          Complex.I * (D (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ)) := by
  let c := (Algebra.TensorProduct.basis ℂ b).equivFun y
  let u := b3Rest2_uR (Module.finrank_self ℂ) b c
  let v := b3Rest2_uI (Module.finrank_self ℂ) b c
  have hv : v = -(Complex.I • u) := by
    simpa only [neg_smul] using b3Rest2_uI_of_mem_F (Module.finrank_self ℂ) b hy
  have hA : A v = -A (Complex.I • u) := by rw [hv, map_neg]
  have hD : D v = -D (Complex.I • u) := by rw [hv, map_neg]
  rw [b66m_complex_real_period_sum]
  have hAu : A u = ∑ i, (c i).re * A (b3Rest2_θ (Module.finrank_self ℂ) (b i)) := by
    simp only [u, b3Rest2_uR, map_sum, map_smul, smul_eq_mul]
  have hAv : A v = ∑ i, (c i).im * A (b3Rest2_θ (Module.finrank_self ℂ) (b i)) := by
    simp only [v, b3Rest2_uI, map_sum, map_smul, smul_eq_mul]
  have hDu : D u = ∑ i, (c i).re * D (b3Rest2_θ (Module.finrank_self ℂ) (b i)) := by
    simp only [u, b3Rest2_uR, map_sum, map_smul, smul_eq_mul]
  have hDv : D v = ∑ i, (c i).im * D (b3Rest2_θ (Module.finrank_self ℂ) (b i)) := by
    simp only [v, b3Rest2_uI, map_sum, map_smul, smul_eq_mul]
  change -(A (-u) : ℂ) - (D (Complex.I • -u) : ℂ) +
    Complex.I * ((A (Complex.I • -u) : ℂ) - (D (-u) : ℂ)) = _
  rw [← hAu, ← hDv, ← hDu, ← hAv, hA, hD]
  simp only [map_neg, smul_neg, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_add]
  ring


/-- Complexification of two real harmonic period functionals. -/
def b66m_complexPeriodFunctional
    (A D : b3_HolForm ℂ (rf8_fibre R.C t) →ₗ[ℝ] ℝ) :
    (ℂ ⊗[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t)) →ₗ[ℂ] ℂ :=
  LinearMap.liftBaseChange ℂ
    (((Complex.ofRealCLM.toLinearMap.comp A).toAddMonoidHom.comp
        (b3Rest2_θHom (Module.finrank_self ℂ)) +
      Complex.I • ((Complex.ofRealCLM.toLinearMap.comp D).toAddMonoidHom.comp
        (b3Rest2_θHom (Module.finrank_self ℂ)))).toIntLinearMap)

/-- On an integral lattice vector the complexification retains both real components. -/
theorem b66m_complexPeriodFunctional_tmul
    (A D : b3_HolForm ℂ (rf8_fibre R.C t) →ₗ[ℝ] ℝ)
    (c : ℂ) (l : b3_periodLattice ℂ (rf8_fibre R.C t)) :
    b66m_complexPeriodFunctional R t A D (c ⊗ₜ[ℤ] l) =
      c * ((A (b3Rest2_θ (Module.finrank_self ℂ) l) : ℂ) +
        Complex.I * (D (b3Rest2_θ (Module.finrank_self ℂ) l) : ℂ)) := by
  rw [b66m_complexPeriodFunctional, LinearMap.liftBaseChange_tmul]
  rfl

/-- The basis sum for the trace is the same intrinsic complex period functional. -/
theorem b66m_complexPeriodFunctional_coords
    (A D : b3_HolForm ℂ (rf8_fibre R.C t) →ₗ[ℝ] ℝ)
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t)) :
    b66m_complexPeriodFunctional R t A D y =
      ∑ i, (Algebra.TensorProduct.basis ℂ b).equivFun y i *
        ((A (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ) +
          Complex.I * (D (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ)) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis ℂ b).sum_equivFun y]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, b3Rest2_tmulBasis (Module.finrank_self ℂ) b,
    b66m_complexPeriodFunctional_tmul]
  simp only [one_mul, smul_eq_mul]

/-- The retained polygon at its base parameter represents the original loop class. -/
theorem b66m_retained_loopClass {c : ℝ → R.C} (hc : Continuous c)
    (hcp : Function.Periodic c 1)
    (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ))) :
    b6m_loopClass (rf8_fibre R.C t)
      (K.loopF (b6t_polydisc mr_base) (Subset.refl _) t (R.hincl t) K.cond_u₀) =
      b63e_fibreLoopClass mr_base R.C t hc hcp := by
  rw [b63e_loopClass_eq_fibreLoopClass_param]
  have hhom : Continuous fun p : unitInterval × ℝ => (K.hom p).2 :=
    continuous_snd.comp K.continuous_hom
  have hhomp : ∀ l, Function.Periodic (fun τ => (K.hom (l, τ)).2) 1 :=
    fun l τ => by simp only [K.hom_periodic l τ]
  have hd : Continuous fun τ => (K.floorLoop t.val ((K.N : ℝ) * τ)).2 := by
    have hh := hhom.comp (continuous_const.prodMk continuous_id :
      Continuous fun τ : ℝ => ((1 : unitInterval), τ))
    exact hh.congr fun τ => congrArg Prod.snd (K.hom_one τ)
  have hdp : Function.Periodic (fun τ => (K.floorLoop t.val ((K.N : ℝ) * τ)).2) 1 :=
    fun τ => by simp only [K.floorLoop_periodic _ τ]
  have he := b63e_fibreLoopClass_homotopy' mr_base R.C t _ hhom hhomp hc hcp hd hdp
    (fun τ => by rw [K.hom_zero]) (fun τ => by rw [K.hom_one])
  apply Eq.trans ?_ he.symm
  apply b63e_fibreLoopClass_congr
  intro τ
  exact congrArg Prod.snd (K.loopF_val (b6t_polydisc mr_base) (Subset.refl _)
    t (R.hincl t) K.cond_u₀ τ)

section ParameterFunctional
variable {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R) (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66g_forms R t 1)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})

/-- The actual scalar de Rham pairing as a real linear functional on holomorphic forms. -/
def b66m_correctedParameterHolPairing (L : ℂ →L[ℝ] ℝ) :
    b3_HolForm ℂ (rf8_fibre R.C t) →ₗ[ℝ] ℝ :=
  ((b3Forms_closedPairing (b3Rest_b (Module.finrank_self ℂ)))
    (b66m_correctedParameterClosedForm R t θ q h ρ hU ht hqf hq hρ L)).comp
      (b3Forms_reClosed (Module.finrank_self ℂ))

theorem b66m_correctedParameterHolPairing_apply (L : ℂ →L[ℝ] ℝ)
    (η : b3_HolForm ℂ (rf8_fibre R.C t)) :
    b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ L η =
      b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (b66m_correctedParameterScalarForm R t θ q h ρ L) (b3Forms_reForm η) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The harmonic pairing gives the derivative on every original integral homology class. -/
theorem b66m_correctedParameterHolPairing_flat (s : b6t_polydisc mr_base)
    (L : ℂ →L[ℝ] ℝ) (x : b66g_Homology R s) :
    b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ L
      (b3Rest2_θ (Module.finrank_self ℂ)
        (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) x))) =
      L (fderiv ℂ (b63e_periodFunction mr_base R.C (b6t_polydisc mr_base)
        (Subset.refl _) R.P θ s x) t.val h) := by
  obtain ⟨γ, rfl⟩ := b6m_smooth_loopClass_surjective (rf8_fibre R.C s) x
  let c : ℝ → R.C := fun τ => (γ.val τ).val.2
  have hc : Continuous c :=
    continuous_snd.comp (continuous_subtype_val.comp γ.property.2.continuous)
  have hcp : Function.Periodic c 1 := fun τ => by
    change (γ.val (τ + 1)).val.2 = (γ.val τ).val.2
    rw [γ.property.1 τ]
  obtain ⟨K, a, hφ, ha⟩ := b66m_retained_cover R t hc hcp
  have he : b6m_loopClass (rf8_fibre R.C s) γ =
      b63e_fibreLoopClass mr_base R.C s hc hcp :=
    b63e_loopClass_eq_fibreLoopClass_param mr_base R.C (b6t_polydisc mr_base)
      (Subset.refl _) s γ
  rw [he, b63e_fibreLoopClass_transport]
  rw [← b66m_retained_loopClass R t hc hcp K, R.hP]
  exact b66m_correctedParameterScalarForm_flat_pairing R t θ q h ρ hU ht hqf hq hρ
    s L hc hcp K a hφ ha

/-- The Cech trace on a polarized full-filtration form is the complexified period functional. -/
theorem b66m_contraction_cech_full_functional
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t))
    (hy : y ∈ b3_periodF ℂ (rf8_fibre R.C t)) :
    b66m_cechTrace R t ρ hρ (b66m_sc_cechProjection R t
      ⟨b66g_contract R q (b66k_cocycle R t h),
        b66m_rs_contract_mem R t hqf (b66k_cocycle_mem R t h)⟩)
      (b66m_polarizedHarmonicForm R t b y) =
    ∑ i, (Algebra.TensorProduct.basis ℂ b).equivFun y i *
      ((b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.reCLM
        (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ) +
      Complex.I * (b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.imCLM
        (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ)) := by
  rw [b66m_cechTrace_cycle]
  change b66m_dolbeaultIntegral R t (b66m_contractionSmooth01 R t q h ρ hqf hρ) _ = _
  rw [b66m_contraction_dolbeault_pairing R t θ q h ρ hU ht hqf hq hρ]
  exact b66m_polarizedHarmonicForm_functional R t b
    (b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.reCLM)
    (b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.imCLM) y hy

/-- The Cech trace uses the intrinsic complexification, independently of basis coordinates. -/
theorem b66m_contraction_cech_functional
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t))
    (hy : y ∈ b3_periodF ℂ (rf8_fibre R.C t)) :
    b66m_cechTrace R t ρ hρ (b66m_sc_cechProjection R t
      ⟨b66g_contract R q (b66k_cocycle R t h),
        b66m_rs_contract_mem R t hqf (b66k_cocycle_mem R t h)⟩)
      (b66m_polarizedHarmonicForm R t b y) =
    b66m_complexPeriodFunctional R t
      (b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.reCLM)
      (b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.imCLM) y := by
  rw [b66m_contraction_cech_full_functional R t b θ q h ρ hU ht hqf hq hρ y hy,
    b66m_complexPeriodFunctional_coords R t b]

end ParameterFunctional

end HodgeLean.Foundations.Program

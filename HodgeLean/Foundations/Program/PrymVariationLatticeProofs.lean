import HodgeLean.Foundations.Program.PrymVariationLatticeSchur

set_option maxHeartbeats 400000

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b63l_projectorCoeff_cast_aux (g : b4b_Group) :
    (b4b_projectorCoeff g : ℝ) = 6 * (b4b_toMatrix g⁻¹ 0 0).re := by
  have omega_re : g32h_omega.re = -(1 / 2 : ℝ) := by
    have harg : 2 * Real.pi * Complex.I / 3 = (2 * Real.pi / 3 : ℝ) * Complex.I := by
      push_cast
      ring
    rw [g32h_omega, harg, Complex.exp_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.mul_im,
      Complex.ofReal_im, Complex.I_im, mul_one, add_zero]
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_sub]
    rw [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
    norm_num
  have omega_im_sq : g32h_omega.im ^ 2 = (3 / 4 : ℝ) := by
    have h := congrArg Complex.re g32h_omega_sq_add
    simp only [Complex.add_re, Complex.one_re, pow_two, Complex.mul_re] at h
    rw [omega_re] at h
    norm_num at h
    nlinarith
  have closure_lift (X : Matrix (Fin 4) (Fin 4) ℂ)
      (hX : X ∈ Submonoid.closure
        (HurwitzPrymRex_img g32h_omega HurwitzPrymRex_g32SOne)) :
      ∃ A : HurwitzPrymRex_Mat, HurwitzPrymRex_evM g32h_omega A = X := by
    induction hX using Submonoid.closure_induction with
    | mem X hX =>
        rcases hX with ⟨A, _, rfl⟩
        exact ⟨A, rfl⟩
    | one => exact ⟨HurwitzPrymRex_mone, HurwitzPrymRex_evM_mone⟩
    | mul X Y _ _ hX hY =>
        rcases hX with ⟨A, rfl⟩
        rcases hY with ⟨B, rfl⟩
        exact ⟨HurwitzPrymRex_mmul A B,
          HurwitzPrymRex_evM_mmul g32h_omega_sq_add A B⟩
  have cast_lift (A : HurwitzPrymRex_Mat) :
      ∃ n : ℤ, (n : ℝ) = 6 *
        (HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega A) 0 0).re := by
    let a := A 0 0
    let b := A 0 1
    let c := A 0 2
    let d := A 0 3
    refine ⟨6 * a.re - 6 * b.re + 3 * d.re - 3 * a.om + 3 * b.om - 3 * c.om, ?_⟩
    simp [HurwitzPrymRex_g32conj, HurwitzPrymRex_g32P, HurwitzPrymRex_g32Pinv,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, HurwitzPrymRex_evM,
      HurwitzPrymRex_ev, omega_re, a, b, c, d]
    ring_nf
    rw [omega_im_sq]
    ring
  have hg : b4b_toMatrix g⁻¹ ∈ g32h_G := (g⁻¹).property
  have hGeq := congrArg
    (fun H : Submonoid (Matrix (Fin 4) (Fin 4) ℂ) ↦ b4b_toMatrix g⁻¹ ∈ H)
    HurwitzPrymRex_g32_G_eq
  have hg' := hGeq.mp hg
  rcases hg' with ⟨X, hX, hconj⟩
  rcases closure_lift X hX with ⟨A, rfl⟩
  rcases cast_lift A with ⟨n, hn⟩
  rw [hconj] at hn
  unfold b4b_projectorCoeff
  change (⌊6 * (b4b_toMatrix g⁻¹ 0 0).re⌋ : ℝ) = _
  rw [← hn]
  norm_num

theorem b63l_projectorCoeff_inverse_aux (g : b4b_Group) :
    b4b_projectorCoeff g⁻¹ = b4b_projectorCoeff g := by
  have hre : (b4b_toMatrix g⁻¹ 0 0).re = (b4b_toMatrix g 0 0).re := by
    rw [b63l_toMatrix_inv_eq_star]
    rfl
  unfold b4b_projectorCoeff
  rw [inv_inv, hre]

theorem b63l_projectorCoeff_complex (g : b4b_Group) :
    (b4b_projectorCoeff g : ℂ) =
      3 * (b4b_toMatrix g 0 0 + starRingEnd ℂ (b4b_toMatrix g 0 0)) := by
  have hr : ((b4b_projectorCoeff g : ℝ) : ℂ) = ((6 * (b4b_toMatrix g⁻¹ 0 0).re : ℝ) : ℂ) := by
    rw [b63l_projectorCoeff_cast_aux]
  rw [b63l_toMatrix_entry_inv, Complex.conj_re] at hr
  push_cast at hr
  rw [hr, Complex.re_eq_add_conj]
  ring

theorem b63l_projector_matrix_aux  :
    ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4b_toMatrix g =
      (b4b_projectorDenominator : ℂ) •
        (Matrix.single 0 0 1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hent (A M : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
      (A * (Matrix.single b 0 (1 : ℂ) : Matrix (Fin 4) (Fin 4) ℂ) * M) a 0 = A a b * M 0 0 := by
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]
  have hz (a b : Fin 4) :
      ∑ g : b4b_Group, b4b_toMatrix g a b * b4b_toMatrix g 0 0 = 0 := by
    have h := congrFun (congrFun (b63l_average_zero (Matrix.single b 0 1)) a) 0
    simpa only [Matrix.sum_apply, hent, Matrix.transpose_apply, Matrix.zero_apply] using h
  have hs (a b : Fin 4) :
      ∑ g : b4b_Group, b4b_toMatrix g a b * starRingEnd ℂ (b4b_toMatrix g 0 0) =
        if a = 0 ∧ b = 0 then 38880 else 0 := by
    have h := congrFun (congrFun (b63l_average_scalar (Matrix.single b 0 1)) a) 0
    simp only [Matrix.sum_apply, hent, b63l_toMatrix_entry_inv] at h
    have htr : (Matrix.single b 0 1 : Matrix (Fin 4) (Fin 4) ℂ).trace =
        if b = 0 then 1 else 0 := by
      fin_cases b <;> simp [Matrix.trace]
    rw [h, htr, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> norm_num [ha, hb]
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, b63l_projectorCoeff_complex]
  have hsplit (g : b4b_Group) :
      3 * (b4b_toMatrix g 0 0 + starRingEnd ℂ (b4b_toMatrix g 0 0)) * b4b_toMatrix g a b =
        3 * (b4b_toMatrix g a b * b4b_toMatrix g 0 0) +
          3 * (b4b_toMatrix g a b * starRingEnd ℂ (b4b_toMatrix g 0 0)) := by
    ring
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hz, hs]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    norm_num [ha, hb, @eq_comm _ (0 : Fin 4), b4b_projectorDenominator]

theorem b63l_projector_convolution_aux (h : b4b_Group) :
    ∑ g : b4b_Group, b4b_projectorCoeff g * b4b_projectorCoeff (g⁻¹ * h) =
      b4b_projectorDenominator * b4b_projectorCoeff h := by
  apply Int.cast_injective (α := ℂ)
  push_cast
  set w : b4b_Group → ℂ := fun g ↦ (b4b_toMatrix h⁻¹ * b4b_toMatrix g) 0 0 with hw
  have hM : ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) * w g =
      (b4b_projectorDenominator : ℂ) * b4b_toMatrix h⁻¹ 0 0 := by
    have hm := congrArg (fun M ↦ (b4b_toMatrix h⁻¹ * M) 0 0) b63l_projector_matrix_aux
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul] at hm
    rw [hw]
    simp only
    rw [hm]
    simp [Matrix.mul_apply, Matrix.single_apply]
  have hterm (g : b4b_Group) :
      (b4b_projectorCoeff g : ℂ) * (b4b_projectorCoeff (g⁻¹ * h) : ℂ) =
        3 * ((b4b_projectorCoeff g : ℂ) * w g) +
          3 * starRingEnd ℂ ((b4b_projectorCoeff g : ℂ) * w g) := by
    rw [← b63l_projectorCoeff_inverse_aux (g⁻¹ * h), mul_inv_rev, inv_inv,
      b63l_projectorCoeff_complex (h⁻¹ * g)]
    simp only [hw, map_mul, map_intCast]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← map_sum, hM,
    b63l_projectorCoeff_complex h, b63l_toMatrix_entry_inv, map_mul, map_intCast,
    Complex.conj_conj]
  ring

theorem b63l_fibreOperator_sq_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) (x : b6m_H1 (b6m_Fibre b C t)) :
    b63l_fibreOperator b C hC t (b63l_fibreOperator b C hC t x) =
      b4b_projectorDenominator • b63l_fibreOperator b C hC t x := by
  have hcomp (g k : b4b_Group) (z : b6m_H1 (b6m_Fibre b C t)) :
      homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ g • q,
        (b6m_deck b b4b_Group C hC t g).continuous⟩)
          (homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ k • q,
            (b6m_deck b b4b_Group C hC t k).continuous⟩) z) =
      homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ (g * k) • q,
        (b6m_deck b b4b_Group C hC t (g * k)).continuous⟩) z := by
    rw [← LinearMap.comp_apply, ← homologyMap_comp]
    congr 2
    ext q
    exact (mul_smul g k q).symm
  have hterm (g k : b4b_Group) (z : b6m_H1 (b6m_Fibre b C t)) :
      (b4b_projectorCoeff g • homologyMap ℤ 1
        (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ g • q,
          (b6m_deck b b4b_Group C hC t g).continuous⟩))
          ((b4b_projectorCoeff k • homologyMap ℤ 1
            (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ k • q,
              (b6m_deck b b4b_Group C hC t k).continuous⟩)) z) =
      (b4b_projectorCoeff g * b4b_projectorCoeff k) •
        homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ (g * k) • q,
          (b6m_deck b b4b_Group C hC t (g * k)).continuous⟩) z := by
    change b4b_projectorCoeff g •
      (homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ g • q,
        (b6m_deck b b4b_Group C hC t g).continuous⟩)
        (b4b_projectorCoeff k • homologyMap ℤ 1
          (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ k • q,
            (b6m_deck b b4b_Group C hC t k).continuous⟩) z)) = _
    rw [map_zsmul, smul_smul, hcomp]
  have hsum_right (f : b4b_Group → ℤ) (v : b6m_H1 (b6m_Fibre b C t)) :
      (∑ g : b4b_Group, f g) • v = ∑ g : b4b_Group, f g • v := by
    induction (Finset.univ : Finset b4b_Group) using Finset.induction_on with
    | empty => exact zero_zsmul v
    | @insert g s hg ih => simp only [Finset.sum_insert hg, add_zsmul, ih]
  have hsum_left (n : ℤ) (f : b4b_Group → b6m_H1 (b6m_Fibre b C t)) :
      n • (∑ g : b4b_Group, f g) = ∑ g : b4b_Group, n • f g := by
    induction (Finset.univ : Finset b4b_Group) using Finset.induction_on with
    | empty => exact zsmul_zero n
    | @insert g s hg ih => simp only [Finset.sum_insert hg, zsmul_add, ih]
  simp only [b63l_fibreOperator, b63l_homologyOperator, LinearMap.sum_apply, map_sum,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  simp_rw [hterm]
  have hreindex (g : b4b_Group) :
      (∑ k : b4b_Group, (b4b_projectorCoeff g * b4b_projectorCoeff k) •
        homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ (g * k) • q,
          (b6m_deck b b4b_Group C hC t (g * k)).continuous⟩) x) =
      ∑ h : b4b_Group, (b4b_projectorCoeff g * b4b_projectorCoeff (g⁻¹ * h)) •
        homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ h • q,
          (b6m_deck b b4b_Group C hC t h).continuous⟩) x := by
    simpa only [inv_mul_cancel_left] using
      Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ (fun k ↦ by simp)
  simp_rw [hreindex]
  rw [Finset.sum_comm]
  calc
    _ = ∑ h : b4b_Group, b4b_projectorDenominator •
        ((b4b_projectorCoeff h • homologyMap ℤ 1
          (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ h • q,
            (b6m_deck b b4b_Group C hC t h).continuous⟩)) x) := by
      apply Finset.sum_congr rfl
      intro h _
      let v := homologyMap ℤ 1
        (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ h • q,
          (b6m_deck b b4b_Group C hC t h).continuous⟩) x
      change (∑ g : b4b_Group,
        (b4b_projectorCoeff g * b4b_projectorCoeff (g⁻¹ * h)) • v) =
          b4b_projectorDenominator • (b4b_projectorCoeff h • v)
      calc
        _ = (∑ g : b4b_Group,
            b4b_projectorCoeff g * b4b_projectorCoeff (g⁻¹ * h)) • v :=
          (hsum_right (fun g ↦
            b4b_projectorCoeff g * b4b_projectorCoeff (g⁻¹ * h)) v).symm
        _ = _ := by rw [b63l_projector_convolution_aux h, mul_smul]
    _ = _ := by
      exact (hsum_left b4b_projectorDenominator (fun h : b4b_Group ↦
        ((b4b_projectorCoeff h • homologyMap ℤ 1
          (TopCat.ofHom ⟨fun q : b6m_Fibre b C t ↦ h • q,
            (b6m_deck b b4b_Group C hC t h).continuous⟩)) x))).symm

theorem b63l_fibre_primitive_rationalization_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (s t : b6t_polydisc b) :
    (∀ (n : ℤ), n ≠ 0 → ∀ x : b6m_H1 (b6m_Fibre b C s),
      n • x ∈ b63l_fibreLattice b C hC s → x ∈ b63l_fibreLattice b C hC s) ∧
    Function.Injective (b63l_fibreRationalInclusion b C hC s) ∧
    LinearMap.range (b63l_fibreRationalInclusion b C hC s) =
      LinearMap.range (b63l_fibreProjector b C hC s) ∧
    (∀ x, b63l_fibreProjector b C hC s (b63l_fibreProjector b C hC s x) =
      b63l_fibreProjector b C hC s x) ∧
    (∀ x : b6m_H1 (b6m_Fibre b C s),
      b6m_H1Equiv (b6m_transport b C s t) x ∈ b63l_fibreLattice b C hC t ↔
        x ∈ b63l_fibreLattice b C hC s) ∧
    (∀ y : b6m_H1 (b6m_Fibre b C t),
      b6m_H1Equiv (b6m_transport b C t s) y ∈ b63l_fibreLattice b C hC s ↔
        y ∈ b63l_fibreLattice b C hC t) := by
  let M := b6m_H1 (b6m_Fibre b C s)
  let f := b63l_fibreOperator b C hC s
  let L := b63l_fibreLattice b C hC s
  have hbase : L.baseChange ℚ = (LinearMap.range f).baseChange ℚ := by
    apply le_antisymm
    · rw [Submodule.baseChange_eq_span]
      apply Submodule.span_le.2
      rintro z ⟨x, hx, rfl⟩
      rcases hx with ⟨n, hn, hx⟩
      change (1 ⊗ₜ[ℤ] x : ℚ ⊗[ℤ] M) ∈ (LinearMap.range f).baseChange ℚ
      letI : TensorProduct.CompatibleSMul ℤ ℤ ℚ M :=
        ⟨fun m q y ↦
          (TensorProduct.CompatibleSMul.int.smul_tmul m q y).trans
            (congrArg (fun z : M ↦ q ⊗ₜ[ℤ] z) (Int.cast_smul_eq_zsmul ℤ m y).symm)⟩
      convert (LinearMap.range f).tmul_mem_baseChange_of_mem (n : ℚ)⁻¹ hx using 1
      rw [TensorProduct.tmul_smul]
      change (1 : ℚ) ⊗ₜ[ℤ] x = ((n : ℚ) * (n : ℚ)⁻¹) ⊗ₜ[ℤ] x
      rw [mul_inv_cancel₀ (show (n : ℚ) ≠ 0 by exact_mod_cast hn)]
    · apply Submodule.baseChange_mono (A := ℚ)
      intro x hx
      exact ⟨1, one_ne_zero, (LinearMap.range f).smul_mem 1 hx⟩
  have hsq : f ∘ₗ f = b4b_projectorDenominator • f := by
    ext x
    exact b63l_fibreOperator_sq_aux b C hC s x
  have hsqQ : f.baseChange ℚ ∘ₗ f.baseChange ℚ =
      (b4b_projectorDenominator : ℚ) • f.baseChange ℚ := by
    ext x
    change f.baseChange ℚ (f.baseChange ℚ (1 ⊗ₜ[ℤ] x)) =
      (b4b_projectorDenominator : ℚ) • f.baseChange ℚ (1 ⊗ₜ[ℤ] x)
    simp only [LinearMap.baseChange_tmul]
    rw [b63l_fibreOperator_sq_aux b C hC s x]
    letI : TensorProduct.CompatibleSMul ℤ ℤ ℚ M :=
      ⟨fun m q y ↦
        (TensorProduct.CompatibleSMul.int.smul_tmul m q y).trans
          (congrArg (fun z : M ↦ q ⊗ₜ[ℤ] z) (Int.cast_smul_eq_zsmul ℤ m y).symm)⟩
    rw [← Int.cast_smul_eq_zsmul ℤ, TensorProduct.tmul_smul]
    change ((b4b_projectorDenominator : ℚ) • (1 : ℚ)) ⊗ₜ[ℤ] f x = _
    congr 1
  have hd : (b4b_projectorDenominator : ℚ) ≠ 0 := by norm_num [b4b_projectorDenominator]
  letI : Module ℤ f.range := f.range.module
  have hrangeF : LinearMap.range (f.range.subtype.baseChange ℚ) =
      LinearMap.range (f.baseChange ℚ) := by
    have hsurj : Function.Surjective (f.rangeRestrict.baseChange ℚ) :=
      LinearMap.baseChange_surjective ℚ (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict f))
    have hfac : f.baseChange ℚ =
        f.range.subtype.baseChange ℚ ∘ₗ f.rangeRestrict.baseChange ℚ := by
      rw [← LinearMap.baseChange_comp]
      rfl
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rcases hsurj x with ⟨z, rfl⟩
      exact ⟨z, by rw [hfac, LinearMap.comp_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨f.rangeRestrict.baseChange ℚ x, by rw [hfac, LinearMap.comp_apply]⟩
  have hrange : LinearMap.range (b63l_fibreRationalInclusion b C hC s) =
      LinearMap.range (b63l_fibreProjector b C hC s) := by
    rw [show LinearMap.range (b63l_fibreRationalInclusion b C hC s) = L.baseChange ℚ by
      rfl, hbase]
    change LinearMap.range (f.range.subtype.baseChange ℚ) = _
    rw [hrangeF]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(b4b_projectorDenominator : ℚ) • x, ?_⟩
      simp only [b63l_fibreProjector, LinearMap.smul_apply, map_smul, smul_smul]
      rw [mul_inv_cancel₀ hd, one_smul]
    · rintro ⟨x, rfl⟩
      exact ⟨(b4b_projectorDenominator : ℚ)⁻¹ • x, by
        change f.baseChange ℚ ((b4b_projectorDenominator : ℚ)⁻¹ • x) =
          (((b4b_projectorDenominator : ℚ)⁻¹ • f.baseChange ℚ) x)
        rw [map_smul, LinearMap.smul_apply]⟩
  have hproj (x : ℚ ⊗[ℤ] M) :
      b63l_fibreProjector b C hC s (b63l_fibreProjector b C hC s x) =
        b63l_fibreProjector b C hC s x := by
    change ((b4b_projectorDenominator : ℚ)⁻¹ • f.baseChange ℚ)
      (((b4b_projectorDenominator : ℚ)⁻¹ • f.baseChange ℚ) x) =
        ((b4b_projectorDenominator : ℚ)⁻¹ • f.baseChange ℚ) x
    simp only [LinearMap.smul_apply, map_smul, smul_smul]
    have hx := LinearMap.congr_fun hsqQ x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hx
    rw [hx, smul_smul]
    field_simp
  let E := b6m_H1Equiv (b6m_transport b C s t)
  let F := b6m_H1Equiv (b6m_transport b C t s)
  have hEF : E.symm = F := by rfl
  have hcomm (x : b6m_H1 (b6m_Fibre b C s)) :
      E (b63l_fibreOperator b C hC s x) = b63l_fibreOperator b C hC t (E x) := by
    simp only [E, b63l_fibreOperator, b63l_homologyOperator, LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro g _
    convert congrArg (b4b_projectorCoeff g • ·)
      (b6m_homology_equivariant b b4b_Group C hC s t g x).2 using 1 <;>
      first | rfl | exact map_zsmul E (b4b_projectorCoeff g) _
  have hcomm' (x : b6m_H1 (b6m_Fibre b C t)) :
      F (b63l_fibreOperator b C hC t x) = b63l_fibreOperator b C hC s (F x) := by
    simp only [F, b63l_fibreOperator, b63l_homologyOperator, LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro g _
    convert congrArg (b4b_projectorCoeff g • ·)
      (b6m_homology_equivariant b b4b_Group C hC t s g x).2 using 1 <;>
      first | rfl | exact map_zsmul F (b4b_projectorCoeff g) _
  have hmem (x : b6m_H1 (b6m_Fibre b C s))
      (hx : x ∈ b63l_fibreLattice b C hC s) :
      E x ∈ b63l_fibreLattice b C hC t := by
    rcases hx with ⟨n, hn, y, hy⟩
    refine ⟨n, hn, E y, ?_⟩
    calc
      b63l_fibreOperator b C hC t (E y) = E (b63l_fibreOperator b C hC s y) := (hcomm y).symm
      _ = E ((inferInstance : Module ℤ (b6m_H1 (b6m_Fibre b C s))).smul n x) := congrArg E hy
      _ = (inferInstance : Module ℤ (b6m_H1 (b6m_Fibre b C t))).smul n (E x) := E.map_smul n x
  have hmem' (x : b6m_H1 (b6m_Fibre b C t))
      (hx : x ∈ b63l_fibreLattice b C hC t) :
      F x ∈ b63l_fibreLattice b C hC s := by
    rcases hx with ⟨n, hn, y, hy⟩
    refine ⟨n, hn, F y, ?_⟩
    calc
      b63l_fibreOperator b C hC s (F y) = F (b63l_fibreOperator b C hC t y) := (hcomm' y).symm
      _ = F ((inferInstance : Module ℤ (b6m_H1 (b6m_Fibre b C t))).smul n x) := congrArg F hy
      _ = (inferInstance : Module ℤ (b6m_H1 (b6m_Fibre b C s))).smul n (F x) := F.map_smul n x
  refine ⟨?_, b63l_subtype_baseChange_rat_injective L, hrange, hproj, ?_, ?_⟩
  · intro n hn x hx
    rw [← Int.cast_smul_eq_zsmul ℤ] at hx
    exact b63l_mem_saturation_of_smul_mem (LinearMap.range f) n hn x hx
  · intro x
    constructor
    · intro hx
      have hm := hmem' (E x) hx
      change F (E x) ∈ b63l_fibreLattice b C hC s at hm
      rw [← hEF] at hm
      simpa using hm
    · exact hmem x
  · intro y
    constructor
    · intro hy
      have hm := hmem (F y) hy
      change E (F y) ∈ b63l_fibreLattice b C hC t at hm
      rw [← hEF] at hm
      simpa using hm
    · exact hmem' y

theorem b63l_fibre_image_transport_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (s t : b6t_polydisc b) :
    (∀ x : b6m_H1 (b6m_Fibre b C s),
      b6m_H1Equiv (b6m_transport b C s t) (b63l_fibreOperator b C hC s x) =
        b63l_fibreOperator b C hC t (b6m_H1Equiv (b6m_transport b C s t) x)) ∧
    ∃ T : b63l_fibreLattice b C hC s ≃ₗ[ℤ] b63l_fibreLattice b C hC t,
      (∀ x, (T x).val = b6m_H1Equiv (b6m_transport b C s t) x.val) ∧
      (∀ y, (T.symm y).val = b6m_H1Equiv (b6m_transport b C t s) y.val) := by
  let E := b6m_H1Equiv (b6m_transport b C s t)
  let F := b6m_H1Equiv (b6m_transport b C t s)
  have hcomm (x : b6m_H1 (b6m_Fibre b C s)) :
      E (b63l_fibreOperator b C hC s x) =
        b63l_fibreOperator b C hC t (E x) := by
    simp only [E, b63l_fibreOperator, b63l_homologyOperator, LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro g _
    convert congrArg (b4b_projectorCoeff g • ·)
      (b6m_homology_equivariant b b4b_Group C hC s t g x).2 using 1 <;>
      first | rfl | exact map_zsmul E (b4b_projectorCoeff g) _
  have hcomm' (x : b6m_H1 (b6m_Fibre b C t)) :
      F (b63l_fibreOperator b C hC t x) =
        b63l_fibreOperator b C hC s (F x) := by
    simp only [F, b63l_fibreOperator, b63l_homologyOperator, LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro g _
    convert congrArg (b4b_projectorCoeff g • ·)
      (b6m_homology_equivariant b b4b_Group C hC t s g x).2 using 1 <;>
      first | rfl | exact map_zsmul F (b4b_projectorCoeff g) _
  have hmem (x : b6m_H1 (b6m_Fibre b C s))
      (hx : x ∈ b63l_fibreLattice b C hC s) :
      E x ∈ b63l_fibreLattice b C hC t := by
    rcases hx with ⟨n, hn, y, hy⟩
    refine ⟨n, hn, E y, ?_⟩
    calc
      b63l_fibreOperator b C hC t (E y) = E (b63l_fibreOperator b C hC s y) := (hcomm y).symm
      _ = E ((inferInstance : Module ℤ (b6m_H1 (b6m_Fibre b C s))).smul n x) := congrArg E hy
      _ = (inferInstance : Module ℤ (b6m_H1 (b6m_Fibre b C t))).smul n (E x) := E.map_smul n x
  have hmem' (x : b6m_H1 (b6m_Fibre b C t))
      (hx : x ∈ b63l_fibreLattice b C hC t) :
      F x ∈ b63l_fibreLattice b C hC s := by
    rcases hx with ⟨n, hn, y, hy⟩
    refine ⟨n, hn, F y, ?_⟩
    calc
      b63l_fibreOperator b C hC s (F y) = F (b63l_fibreOperator b C hC t y) := (hcomm' y).symm
      _ = F ((inferInstance : Module ℤ (b6m_H1 (b6m_Fibre b C t))).smul n x) := congrArg F hy
      _ = (inferInstance : Module ℤ (b6m_H1 (b6m_Fibre b C s))).smul n (F x) := F.map_smul n x
  let T : b63l_fibreLattice b C hC s →ₗ[ℤ] b63l_fibreLattice b C hC t :=
    { toFun := fun x ↦ ⟨E x.val, hmem x.val x.property⟩
      map_add' := fun x y ↦ Subtype.ext (map_add E x.val y.val)
      map_smul' := fun n x ↦ Subtype.ext (map_zsmul E n x.val) }
  let U : b63l_fibreLattice b C hC t →ₗ[ℤ] b63l_fibreLattice b C hC s :=
    { toFun := fun x ↦ ⟨F x.val, hmem' x.val x.property⟩
      map_add' := fun x y ↦ Subtype.ext (map_add F x.val y.val)
      map_smul' := fun n x ↦ Subtype.ext (map_zsmul F n x.val) }
  have hEF : E.symm = F := by
    rfl
  refine ⟨hcomm, ⟨T, U, ?_, ?_⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · intro x
    apply Subtype.ext
    simpa [T, U, ← hEF] using E.symm_apply_apply x.val
  · intro x
    apply Subtype.ext
    simpa [T, U, ← hEF] using E.apply_symm_apply x.val

theorem b63l_period_image_comparison_aux (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    ∃ P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C,
      (∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) ∧
      (∀ x, P (b63l_homologyOperator C (fun g ↦ (hG g).continuous) x) =
        b4_groupEnd ℂ (C := C) b4b_projectorCoeff (P x)) ∧
      ∃ E : b63l_saturation (LinearMap.range (b63l_homologyOperator C (fun g ↦ (hG g).continuous)))
          ≃ₗ[ℤ] b63l_periodLattice C,
        ∀ x, (E x).val = P x.val := by
  obtain ⟨P, hP⟩ := b6m_period_comparison C
  have hdeck (g : b4b_Group) (x : b6m_H1 C) :
      P (homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : C ↦ g • q, (hG g).continuous⟩) x) =
        b4_latticeAct ℂ g (P x) := by
    let e := b4_actionHomeomorph hG g
    have hnat := b6m_period_push_naturality e (hG g) P hP P hP x
    have heq : b3A_push e (hG g) = b4_latticeAct ℂ g :=
      b3A_pushforward_unique e (hG g) _ _
        (b3A_push_isPushforward e (hG g)) (b4_latticeAct_isPushforward hG g)
    rw [heq] at hnat
    exact hnat.symm
  have hcomm (x : b6m_H1 C) :
      P (b63l_homologyOperator C (fun g ↦ (hG g).continuous) x) =
        b4_groupEnd ℂ (C := C) b4b_projectorCoeff (P x) := by
    have sum_apply (s : Finset b4b_Group)
        (f : b4b_Group → b3_periodLattice ℂ C →+ b3_periodLattice ℂ C)
        (z : b3_periodLattice ℂ C) :
        (∑ g ∈ s, f g) z = ∑ g ∈ s, f g z := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert g s hg ih => simp [hg, ih]
    simp only [b63l_homologyOperator, b4_groupEnd, LinearMap.sum_apply,
      map_sum]
    rw [sum_apply]
    apply Finset.sum_congr rfl
    intro g _
    convert congrArg (b4b_projectorCoeff g • ·) (hdeck g x) using 1 <;>
      first | rfl | exact map_zsmul P (b4b_projectorCoeff g) _
  let L := b63l_saturation
    (LinearMap.range (b63l_homologyOperator C (fun g ↦ (hG g).continuous)))
  have hmem (x : b6m_H1 C) (hx : x ∈ L) : P x ∈ b63l_periodLattice C := by
    rcases hx with ⟨n, hn, y, hy⟩
    refine ⟨n, hn, P y, ?_⟩
    calc
      b4_groupEnd ℂ b4b_projectorCoeff (P y) = P (b63l_homologyOperator C (fun g ↦ (hG g).continuous) y) := (hcomm y).symm
      _ = P ((inferInstance : Module ℤ (b6m_H1 C)).smul n x) := congrArg P hy
      _ = (inferInstance : Module ℤ (b3_periodLattice ℂ C)).smul n (P x) := P.map_smul n x
  have hmem' (x : b3_periodLattice ℂ C) (hx : x ∈ b63l_periodLattice C) :
      P.symm x ∈ L := by
    rcases hx with ⟨n, hn, y, hy⟩
    refine ⟨n, hn, P.symm y, ?_⟩
    apply P.injective
    calc
      P (b63l_homologyOperator C (fun g ↦ (hG g).continuous) (P.symm y)) =
          b4_groupEnd ℂ b4b_projectorCoeff y := by simpa using hcomm (P.symm y)
      _ = (inferInstance : Module ℤ (b3_periodLattice ℂ C)).smul n x := hy
      _ = P ((inferInstance : Module ℤ (b6m_H1 C)).smul n (P.symm x)) := by
        symm
        calc
          P ((inferInstance : Module ℤ (b6m_H1 C)).smul n (P.symm x)) =
              (inferInstance : Module ℤ (b3_periodLattice ℂ C)).smul n (P (P.symm x)) :=
                P.map_smul n (P.symm x)
          _ = (inferInstance : Module ℤ (b3_periodLattice ℂ C)).smul n x := by
            rw [P.apply_symm_apply]
  let E : L →ₗ[ℤ] b63l_periodLattice C :=
    { toFun := fun x ↦ ⟨P x.val, hmem x.val x.property⟩
      map_add' := fun x y ↦ Subtype.ext (map_add P x.val y.val)
      map_smul' := fun n x ↦ Subtype.ext (map_zsmul P n x.val) }
  let F : b63l_periodLattice C →ₗ[ℤ] L :=
    { toFun := fun x ↦ ⟨P.symm x.val, hmem' x.val x.property⟩
      map_add' := fun x y ↦ Subtype.ext (map_add P.symm x.val y.val)
      map_smul' := fun n x ↦ Subtype.ext (map_zsmul P.symm n x.val) }
  refine ⟨P, hP, hcomm, ⟨⟨E, F, ?_, ?_⟩, fun _ ↦ rfl⟩⟩
  · intro x
    apply Subtype.ext
    exact P.symm_apply_apply x.val
  · intro x
    apply Subtype.ext
    exact P.apply_symm_apply x.val

theorem b63l_image_riemann_aux (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q) :
    (∀ x y : b3_periodLattice ℂ C,
      Q (b4_groupEnd ℂ b4b_projectorCoeff x) y =
        Q x (b4_groupEnd ℂ b4b_projectorCoeff y)) ∧
    b2_IsWeightOne (b63l_periodLattice C) (b63l_periodF C) ∧
    b2_IsRiemannForm (b63l_periodLattice C) (b63l_periodF C)
      (b63l_periodQ C Q) := by
  constructor
  · intro x y
    rw [b4_groupEnd_adjoint (by norm_num) hG Q hQ b4b_projectorCoeff x y]
    have ha : (fun g : b4b_Group ↦ b4b_projectorCoeff g⁻¹) = b4b_projectorCoeff := by
      funext g
      exact b63l_projectorCoeff_inverse_aux g
    rw [ha]
  constructor
  · let f := (b4_groupEnd ℂ (C := C) b4b_projectorCoeff).toIntLinearMap
    let L := b63l_periodLattice C
    let p := b63l_periodSaturationPresentation C
    let r := p.lift
    have hF := b3_isWeightOne (E := ℂ) (C := C) (by norm_num)
    have hinj := b2a_cplxMap_subtype_injective L.toAddSubgroup
    have himg : ∀ a ∈ b3_periodF ℂ C, r.baseChange ℂ a ∈ b63l_periodF C := by
      intro a ha
      change L.subtype.baseChange ℂ (r.baseChange ℂ a) ∈ b3_periodF ℂ C
      rw [p.compatible]
      exact b4_groupEnd_periodF hG b4b_projectorCoeff ha
    constructor
    · rw [Submodule.disjoint_def]
      intro w hw hw'
      obtain ⟨a, ha, rfl⟩ := b2a_mem_conjSubmodule.1 hw'
      have h1 : L.subtype.baseChange ℂ (b2_conj L a) ∈ b3_periodF ℂ C := hw
      have h2 : L.subtype.baseChange ℂ (b2_conj L a) ∈
          b2_conjSubmodule (b3_periodLattice ℂ C) (b3_periodF ℂ C) := by
        change b2_cplxMap L.subtype.toAddMonoidHom (b2_conj L a) ∈
          b2_conjSubmodule (b3_periodLattice ℂ C) (b3_periodF ℂ C)
        rw [← b2a_conj_cplxMap L.subtype.toAddMonoidHom a]
        exact b2a_conj_mem_conjSubmodule ha
      have hz : L.subtype.baseChange ℂ (b2_conj L a) = 0 := by
        apply (Submodule.mem_bot ℂ).1
        exact hF.disjoint.le_bot (Submodule.mem_inf.2 ⟨h1, h2⟩)
      exact hinj (hz.trans (map_zero _).symm)
    · rw [codisjoint_iff, eq_top_iff]
      intro w _
      rcases p.split w with ⟨⟨a, c⟩, ha, hc, hw⟩
      have hc'' : r.baseChange ℂ (b2_conj (b3_periodLattice ℂ C) c) ∈
          b2_conjSubmodule L (b63l_periodF C) := by
        change b2_cplxMap r.toAddMonoidHom (b2_conj (b3_periodLattice ℂ C) c) ∈
          b2_conjSubmodule L (b63l_periodF C)
        rw [← b2a_conj_cplxMap]
        exact b2a_conj_mem_conjSubmodule (himg c hc)
      rw [← hw]
      exact Submodule.add_mem_sup (himg a ha) hc''
  · let L := b63l_periodLattice C
    have hQR := b3_intersectionForm_isRiemannForm (E := ℂ) (C := C) (by norm_num) Q hQ
    have hinj := b2a_cplxMap_subtype_injective L.toAddSubgroup
    let g := L.subtype.toAddMonoidHom
    have hb : ∀ (u v : ℂ ⊗[ℤ] L),
        LinearMap.BilinForm.baseChange ℂ (b63l_periodQ C Q) u v =
        LinearMap.BilinForm.baseChange ℂ Q (b2_cplxMap g u) (b2_cplxMap g v) :=
      fun u v ↦ b2a_baseChange_compl Q g u v
    refine ⟨fun x ↦ hQR.alt _, fun x hx y hy ↦ ?_, fun x hx hne ↦ ?_⟩
    · rw [hb]
      exact hQR.isotropic (b2_cplxMap g x) hx (b2_cplxMap g y) hy
    · rw [hb, ← b2a_conj_cplxMap]
      exact hQR.positive (b2_cplxMap g x) hx
        fun hz ↦ hne (hinj (hz.trans (map_zero _).symm))

theorem b63l_image_pairing_transport_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D] [MulAction b4b_Group C] [MulAction b4b_Group D]
    (hC : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hD : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : D ↦ g • x))
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (hs : Function.Surjective f)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (heG : ∀ (g : b4b_Group) (x : C), e (g • x) = g • e x)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R) :
    ∃ (P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C)
      (S : b6m_H1 D ≃ₗ[ℤ] b3_periodLattice ℂ D)
      (T : b63l_periodLattice C ≃ₗ[ℤ] b63l_periodLattice D),
      (∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) ∧
      (∀ γ : b3_SmoothLoop ℂ D, S (b6m_loopClass D γ) = b3_latticePeriod ℂ D γ) ∧
      (∀ x, (T x).val = S (b6m_H1Equiv e (P.symm x.val))) ∧
      (∀ y, (T.symm y).val = P (b6m_H1Equiv e.symm (S.symm y.val))) ∧
      ∀ x y, b63l_periodQ D R (T x) (T y) =
        b63l_periodQ C Q x y := by
  obtain ⟨P, S, hP, hS, hpair⟩ :=
    b6m_intersection_transport b hb t ht C D f k hf hk hs e he Q hQ R hR
  let H := b6m_H1Equiv e
  have hhom (g : b4b_Group) (x : b6m_H1 C) :
      H (homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : C ↦ g • q, (hC g).continuous⟩) x) =
        homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : D ↦ g • q, (hD g).continuous⟩) (H x) := by
    let E : TopCat.of C ⟶ TopCat.of D := TopCat.ofHom ⟨e, e.continuous⟩
    let Gc : TopCat.of C ⟶ TopCat.of C :=
      TopCat.ofHom ⟨fun q : C ↦ g • q, (hC g).continuous⟩
    let Gd : TopCat.of D ⟶ TopCat.of D :=
      TopCat.ofHom ⟨fun q : D ↦ g • q, (hD g).continuous⟩
    have hc : Gc ≫ E = E ≫ Gd := by
      ext q
      exact heG g q
    let K := (AlgebraicTopology.singularHomologyFunctor.{0} (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)
    have hm := congrArg (fun u ↦ (K.map u).hom x) hc
    change (K.map E).hom ((K.map Gc).hom x) = (K.map Gd).hom ((K.map E).hom x)
    simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using hm
  have deckC (g : b4b_Group) (x : b6m_H1 C) :
      P (homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : C ↦ g • q, (hC g).continuous⟩) x) =
        b4_latticeAct ℂ g (P x) := by
    let a := b4_actionHomeomorph hC g
    have hn := b6m_period_push_naturality a (hC g) P hP P hP x
    have heq : b3A_push a (hC g) = b4_latticeAct ℂ g :=
      b3A_pushforward_unique a (hC g) _ _ (b3A_push_isPushforward a (hC g))
        (b4_latticeAct_isPushforward hC g)
    rw [heq] at hn
    exact hn.symm
  have deckD (g : b4b_Group) (x : b6m_H1 D) :
      S (homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : D ↦ g • q, (hD g).continuous⟩) x) =
        b4_latticeAct ℂ g (S x) := by
    let a := b4_actionHomeomorph hD g
    have hn := b6m_period_push_naturality a (hD g) S hS S hS x
    have heq : b3A_push a (hD g) = b4_latticeAct ℂ g :=
      b3A_pushforward_unique a (hD g) _ _ (b3A_push_isPushforward a (hD g))
        (b4_latticeAct_isPushforward hD g)
    rw [heq] at hn
    exact hn.symm
  let A : b3_periodLattice ℂ C ≃ₗ[ℤ] b3_periodLattice ℂ D :=
    P.symm.trans (H.trans S)
  have hact (g : b4b_Group) (x : b3_periodLattice ℂ C) :
      A (b4_latticeAct ℂ g x) = b4_latticeAct ℂ g (A x) := by
    change S (H (P.symm (b4_latticeAct ℂ g x))) = _
    calc
      S (H (P.symm (b4_latticeAct ℂ g x))) =
          S (H (homologyMap ℤ 1
            (TopCat.ofHom ⟨fun q : C ↦ g • q, (hC g).continuous⟩) (P.symm x))) := by
              congr 2
              apply P.injective
              rw [P.apply_symm_apply, deckC g (P.symm x), P.apply_symm_apply]
      _ = S (homologyMap ℤ 1
            (TopCat.ofHom ⟨fun q : D ↦ g • q, (hD g).continuous⟩) (H (P.symm x))) :=
              congrArg S (hhom g (P.symm x))
      _ = b4_latticeAct ℂ g (S (H (P.symm x))) := deckD g (H (P.symm x))
  have hcomm (x : b3_periodLattice ℂ C) :
      A (b4_groupEnd ℂ b4b_projectorCoeff x) =
        b4_groupEnd ℂ b4b_projectorCoeff (A x) := by
    simp only [b4_groupEnd]
    have sum_apply (X : Type) [AddCommMonoid X] (u : Finset b4b_Group)
        (v : b4b_Group → X →+ X) (z : X) :
        (∑ g ∈ u, v g) z = ∑ g ∈ u, v g z := by
      induction u using Finset.induction_on with
      | empty => simp
      | @insert g u hg ih => simp [hg, ih]
    rw [sum_apply]
    simp only [map_sum]
    rw [sum_apply]
    apply Finset.sum_congr rfl
    intro g _
    change A (b4b_projectorCoeff g • b4_latticeAct ℂ g x) =
      b4b_projectorCoeff g • b4_latticeAct ℂ g (A x)
    rw [map_zsmul, hact]
  have hmem (x : b3_periodLattice ℂ C) (hx : x ∈ b63l_periodLattice C) :
      A x ∈ b63l_periodLattice D := by
    rcases hx with ⟨n, hn, y, hy⟩
    refine ⟨n, hn, A y, ?_⟩
    calc
      b4_groupEnd ℂ b4b_projectorCoeff (A y) = A (b4_groupEnd ℂ b4b_projectorCoeff y) := (hcomm y).symm
      _ = A ((inferInstance : Module ℤ (b3_periodLattice ℂ C)).smul n x) := congrArg A hy
      _ = (inferInstance : Module ℤ (b3_periodLattice ℂ D)).smul n (A x) := A.map_smul n x
  have hmem' (y : b3_periodLattice ℂ D) (hy : y ∈ b63l_periodLattice D) :
      A.symm y ∈ b63l_periodLattice C := by
    rcases hy with ⟨n, hn, z, hz⟩
    refine ⟨n, hn, A.symm z, ?_⟩
    apply A.injective
    calc
      A (b4_groupEnd ℂ b4b_projectorCoeff (A.symm z)) =
          b4_groupEnd ℂ b4b_projectorCoeff z := by simpa using hcomm (A.symm z)
      _ = (inferInstance : Module ℤ (b3_periodLattice ℂ D)).smul n y := hz
      _ = A ((inferInstance : Module ℤ (b3_periodLattice ℂ C)).smul n (A.symm y)) := by
        symm
        calc
          A ((inferInstance : Module ℤ (b3_periodLattice ℂ C)).smul n (A.symm y)) =
              (inferInstance : Module ℤ (b3_periodLattice ℂ D)).smul n (A (A.symm y)) :=
                A.map_smul n (A.symm y)
          _ = (inferInstance : Module ℤ (b3_periodLattice ℂ D)).smul n y := by
            rw [A.apply_symm_apply]
  let T : b63l_periodLattice C →ₗ[ℤ] b63l_periodLattice D :=
    { toFun := fun x ↦ ⟨A x.val, hmem x.val x.property⟩
      map_add' := fun x y ↦ Subtype.ext (map_add A x.val y.val)
      map_smul' := fun n x ↦ Subtype.ext (map_zsmul A n x.val) }
  let U : b63l_periodLattice D →ₗ[ℤ] b63l_periodLattice C :=
    { toFun := fun x ↦ ⟨A.symm x.val, hmem' x.val x.property⟩
      map_add' := fun x y ↦ Subtype.ext (map_add A.symm x.val y.val)
      map_smul' := fun n x ↦ Subtype.ext (map_zsmul A.symm n x.val) }
  let TE : b63l_periodLattice C ≃ₗ[ℤ] b63l_periodLattice D :=
    ⟨T, U, fun x ↦ Subtype.ext (A.symm_apply_apply x.val),
      fun y ↦ Subtype.ext (A.apply_symm_apply y.val)⟩
  refine ⟨P, S, TE, hP, hS, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
  intro x y
  change R (A x.val) (A y.val) = Q x.val y.val
  simpa [A, H] using hpair (P.symm x.val) (P.symm y.val)

end HodgeLean.Foundations.Program

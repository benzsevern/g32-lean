import HodgeLean.Foundations.Program.CodifferentialComparisonGraphProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonDefs


noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers Metric
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful


set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] b3Forms_isManifold_real
variable {c₀ : Fin 10 → ℂ} {g₀ : Fin 13 → b4b_Group}

def b66f_gen_b66m_polarizedHarmonicForm (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {ι : Type} (b : Module.Basis ι ℤ (b3_periodLattice ℂ (b65z_fibre c₀ R.C t))) [Fintype ι] [DecidableEq ι]
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) :
    b3_HolForm ℂ (b65z_fibre c₀ R.C t) :=
  -b3Rest2_uR (Module.finrank_self ℂ) b ((Algebra.TensorProduct.basis ℂ b).equivFun y)

theorem b66f_gen_b66m_primitive_coefficient_of_holProjector (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i)))  (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (w : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (hw : b66f_gen_b66m_holProjector R t w = (b4b_projectorDenominator : ℂ) • w) :
    ∃ q : b66f_primitiveForms R t, w.val = b66f_chartForm R t q.val := by
  obtain ⟨M, hM, hP⟩ := b66f_gen_b66m_chart_projector hg R t
  obtain ⟨qP, hqP, hwP⟩ := hP (M.symm w)
  have hp : qP.val ∈ b66f_primitiveForms R t :=
    ⟨qP.property, M.symm w, hqP.symm⟩
  let z : ℂ := (b4b_projectorDenominator : ℂ)⁻¹
  let qF : b66f_forms R t 1 := z • qP
  have hqF : qF.val ∈ b66f_primitiveForms R t :=
    (b66f_primitiveForms R t).smul_mem z hp
  have he : M qF = w := by
    change M (z • qP) = w
    rw [map_smul, hwP, M.apply_symm_apply, hw, smul_smul]
    have hd : (b4b_projectorDenominator : ℂ) ≠ 0 := by
      norm_num [b4b_projectorDenominator]
    rw [show z * (b4b_projectorDenominator : ℂ) = 1 from inv_mul_cancel₀ hd, one_smul]
  refine ⟨⟨qF.val, hqF⟩, ?_⟩
  rw [← he]
  exact hM qF

theorem b66f_gen_b66m_intersection_lattice_W (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (l k : b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) :
    (R.Q t l k : ℝ) = b3Rest2_W (Module.finrank_self ℂ)
      (b3Rest2_θ (Module.finrank_self ℂ) l) (b3Rest2_θ (Module.finrank_self ℂ) k) := by
  have he := b3Rest_intersectionForm_unique (Module.finrank_self ℂ) (R.Q t)
    (b3Rest2_QZ (Module.finrank_self ℂ) (b3Rest2_key (Module.finrank_self ℂ)))
    (R.hQ t) (b3Rest2_isIntersectionForm (Module.finrank_self ℂ)
      (b3Rest2_key (Module.finrank_self ℂ)))
  rw [he, b3Rest2_QZ_apply, b3Rest2_Q_eq_W]

theorem b66f_gen_b66m_intersection_right_coords (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {ι : Type} (b : Module.Basis ι ℤ (b3_periodLattice ℂ (b65z_fibre c₀ R.C t))) [Fintype ι] [DecidableEq ι] (l : b3_periodLattice ℂ (b65z_fibre c₀ R.C t))
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) :
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
  have hQ := congrArg (fun r : ℝ => (r : ℂ)) (b66f_gen_b66m_intersection_lattice_W R t l (b i))
  simp only [Complex.ofReal_intCast] at hQ
  rw [hQ]
  change B.equivFun y i * _ = _
  dsimp only [B]
  apply Complex.ext <;> simp <;> ring

theorem b66f_gen_b66m_polarizedHarmonicForm_period (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {ι : Type} (b : Module.Basis ι ℤ (b3_periodLattice ℂ (b65z_fibre c₀ R.C t))) [Fintype ι] [DecidableEq ι]
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t))
    (hy : y ∈ b3_periodF ℂ (b65z_fibre c₀ R.C t))
    (l : b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) :
    l.val (b66f_gen_b66m_polarizedHarmonicForm R t b y) = (R.Q t).baseChange ℂ (1 ⊗ₜ[ℤ] l) y := by
  rw [b66f_gen_b66m_intersection_right_coords R t b,
    b3Rest2_uI_of_mem_F (Module.finrank_self ℂ) b hy]
  rw [b3Rest2_lattice_apply (Module.finrank_self ℂ)]
  simp only [b66f_gen_b66m_polarizedHarmonicForm, map_neg, LinearMap.neg_apply,
    smul_neg, neg_smul]
  let u := b3Rest2_uR (Module.finrank_self ℂ) b ((Algebra.TensorProduct.basis ℂ b).equivFun y)
  rw [b3Rest2_W_skew (Module.finrank_self ℂ) u (b3Rest2_θ (Module.finrank_self ℂ) l),
    b3Rest2_W_skew (Module.finrank_self ℂ) (Complex.I • u) (b3Rest2_θ (Module.finrank_self ℂ) l)]
  push_cast
  ring

theorem b66f_gen_b66m_projector_pairing_complex (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (l : b3_periodLattice ℂ (b65z_fibre c₀ R.C t))
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) :
    (R.Q t).baseChange ℂ (1 ⊗ₜ[ℤ] b4_groupEnd ℂ b4b_projectorCoeff l) y =
      (R.Q t).baseChange ℂ (1 ⊗ₜ[ℤ] l)
        (b2_cplxMap (b4_groupEnd ℂ b4b_projectorCoeff) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul c k =>
    have he := (b63l_image_riemann (b65z_fibre c₀ R.C t) (R.hG t) (R.Q t) (R.hQ t)).1 l k
    simp only [b2_cplxMap, LinearMap.baseChange_tmul,
      LinearMap.BilinForm.baseChange_tmul, one_mul, zsmul_eq_mul,
      AddMonoidHom.coe_toIntLinearMap, he]

theorem b66f_gen_b66m_primitiveFullVector_eigen (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (n : ℂ ⊗[ℤ] b60_Lattice) :
    b2_cplxMap (b4_groupEnd ℂ b4b_projectorCoeff) (b66f_gen_b66m_primitiveFullVector R s t m n) =
      b4b_projectorDenominator • b66f_gen_b66m_primitiveFullVector R s t m n := by
  obtain ⟨v, rfl⟩ := (b64b_complexMarking _ m).surjective n
  simp only [b66f_gen_b66m_primitiveFullVector, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul c x =>
    simp only [LinearMap.baseChange_tmul, b2_cplxMap, AddMonoidHom.coe_toIntLinearMap]
    rw [b66f_gen_b66m_transport_period_eigen]
    exact (map_zsmul (TensorProduct.mk ℤ ℂ
      (b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) c) b4b_projectorDenominator _)

theorem b66f_gen_b66m_primitiveFullVector_holProjector (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i)))  (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (b3_periodLattice ℂ (b65z_fibre c₀ R.C t)))
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b65z_period R s m t.val)) :
    b66f_gen_b66m_holProjector R t
      (b66f_gen_b66m_polarizedHarmonicForm R t b (b66f_gen_b66m_primitiveFullVector R s t m n)) =
      (b4b_projectorDenominator : ℂ) •
        b66f_gen_b66m_polarizedHarmonicForm R t b (b66f_gen_b66m_primitiveFullVector R s t m n) := by
  let y := b66f_gen_b66m_primitiveFullVector R s t m n
  let w := b66f_gen_b66m_polarizedHarmonicForm R t b y
  have hy := b66f_gen_b66m_primitiveFullVector_mem hg R s t m hJ hpol n hn
  have hv (l : b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) :
      l.val (b66f_gen_b66m_holProjector R t w) = (b4b_projectorDenominator : ℂ) * l.val w := by
    rw [b66f_gen_b66m_holProjector_period R t l w]
    rw [b66f_gen_b66m_polarizedHarmonicForm_period R t b y hy,
      b66f_gen_b66m_projector_pairing_complex R t l y,
      b66f_gen_b66m_primitiveFullVector_eigen R s t m n]
    rw [map_zsmul]
    rw [b66f_gen_b66m_polarizedHarmonicForm_period R t b y hy]
    exact Int.cast_smul_eq_zsmul ℂ _ _ |>.symm
  apply sub_eq_zero.mp
  apply b3Rest2_eq_zero_of_re_lattice (Module.finrank_self ℂ)
  intro l
  let L := b3A_toDual ⟨l.val, b3A_lattice_mem_linearDual l⟩
  change (L (b66f_gen_b66m_holProjector R t w - (b4b_projectorDenominator : ℂ) • w)).re = 0
  rw [map_sub, map_smul]
  change (l.val (b66f_gen_b66m_holProjector R t w) - (b4b_projectorDenominator : ℂ) * l.val w).re = 0
  rw [hv, sub_self]
  rfl

theorem b66f_gen_b66m_transport_intersection_W (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀)
    (x y : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s) :
    b3Rest2_W (Module.finrank_self ℂ)
      (b3Rest2_θ (Module.finrank_self ℂ)
        (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) R.P s t x))
      (b3Rest2_θ (Module.finrank_self ℂ)
        (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) R.P s t y)) =
    b3Rest2_W (Module.finrank_self ℂ)
      (b3Rest2_θ (Module.finrank_self ℂ) (R.P s x.val))
      (b3Rest2_θ (Module.finrank_self ℂ) (R.P s y.val)) := by
  rw [← b66f_gen_b66m_intersection_lattice_W, ← b66f_gen_b66m_intersection_lattice_W]
  have he := b63e_pairing_constant c₀ R.C (b6t_polydisc c₀) (Subset.refl _)
    R.atlas.hb R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
    R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP s t x.val y.val
  exact congrArg (fun z : ℤ => (z : ℝ)) he

theorem b66f_gen_b66m_singular_intersection_W (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (x y : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) t) :
    ((b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
      t (R.P t) (R.Q t) x y : ℤ) : ℝ) =
      b3Rest2_W (Module.finrank_self ℂ)
        (b3Rest2_θ (Module.finrank_self ℂ) (R.P t x.val))
        (b3Rest2_θ (Module.finrank_self ℂ) (R.P t y.val)) := by
  exact b66f_gen_b66m_intersection_lattice_W R t (R.P t x.val) (R.P t y.val)

theorem b66f_gen_b66m_marked_intersection_W (R : b65z_SharedFamily c₀ g₀) (s : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (x y : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s) :
    b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
      (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] y)) =
      (b3Rest2_W (Module.finrank_self ℂ)
        (b3Rest2_θ (Module.finrank_self ℂ) (R.P s x.val))
        (b3Rest2_θ (Module.finrank_self ℂ) (R.P s y.val)) : ℂ) := by
  rw [b64b_complex_pairing _ _ m hpol, LinearMap.BilinForm.baseChange_tmul]
  simp only [one_mul, zsmul_eq_mul, mul_one]
  have he := congrArg (fun a : ℝ => (a : ℂ)) (b66f_gen_b66m_singular_intersection_W R s x y)
  simpa only [Complex.ofReal_intCast] using he

theorem b66f_gen_b66m_marked_transport_intersection_W (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (x y : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s) :
    b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
      (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] y)) =
      (b3Rest2_W (Module.finrank_self ℂ)
        (b3Rest2_θ (Module.finrank_self ℂ)
          (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) R.P s t x))
        (b3Rest2_θ (Module.finrank_self ℂ)
          (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) R.P s t y)) : ℂ) := by
  rw [b66f_gen_b66m_transport_intersection_W]
  exact b66f_gen_b66m_marked_intersection_W R s m hpol x y

theorem b66f_gen_b66m_primitiveFullVector_pairing (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (x y : ℂ ⊗[ℤ] b60_Lattice) :
    (R.Q t).baseChange ℂ (b66f_gen_b66m_primitiveFullVector R s t m x)
      (b66f_gen_b66m_primitiveFullVector R s t m y) = b60_E.baseChange ℂ x y := by
  obtain ⟨u, rfl⟩ := (b64b_complexMarking _ m).surjective x
  obtain ⟨v, rfl⟩ := (b64b_complexMarking _ m).surjective y
  simp only [b66f_gen_b66m_primitiveFullVector, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | tmul c a =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add v v' hv hv' => simp only [map_add, hv, hv']
    | tmul d b =>
      have he := b66f_gen_b66m_marked_transport_intersection_W R s t m hpol a b
      rw [← b66f_gen_b66m_intersection_lattice_W] at he
      simp only [Complex.ofReal_intCast] at he
      have hbase : (R.Q t).baseChange ℂ
          ((b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
            (Subset.refl _) R.P s t).baseChange ℂ (1 ⊗ₜ[ℤ] a))
          ((b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
            (Subset.refl _) R.P s t).baseChange ℂ (1 ⊗ₜ[ℤ] b)) =
          b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] a))
            (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] b)) := by
        simpa only [LinearMap.baseChange_tmul, one_smul,
          LinearMap.BilinForm.baseChange_tmul, one_mul, zsmul_eq_mul, mul_one] using he.symm
      rw [show c ⊗ₜ[ℤ] a = c • (1 ⊗ₜ[ℤ] a) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        show d ⊗ₜ[ℤ] b = d • (1 ⊗ₜ[ℤ] b) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hbase]

theorem b66f_gen_b66m_primitiveFullVector_period (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i)))  (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (b3_periodLattice ℂ (b65z_fibre c₀ R.C t)))
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b65z_period R s m t.val))
    (x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s) :
    (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) R.P s t x).val
      (b66f_gen_b66m_polarizedHarmonicForm R t b (b66f_gen_b66m_primitiveFullVector R s t m n)) =
      b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n := by
  rw [b66f_gen_b66m_polarizedHarmonicForm_period R t b _
    (b66f_gen_b66m_primitiveFullVector_mem hg R s t m hJ hpol n hn)]
  have he := b66f_gen_b66m_primitiveFullVector_pairing R s t m hpol
    (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n
  simpa only [b66f_gen_b66m_primitiveFullVector, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.baseChange_tmul, one_smul] using he

end HodgeLean.Foundations.Program

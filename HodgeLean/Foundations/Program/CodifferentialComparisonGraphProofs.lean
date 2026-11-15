import HodgeLean.Foundations.Program.PathCoverFamilyPeriod
import HodgeLean.Foundations.Program.CodifferentialComparisonVariationProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonBasisProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonChartProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonDefs


noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
set_option backward.isDefEq.respectTransparency false
attribute [local instance] b3Forms_isManifold_real
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful


variable {c₀ : Fin 10 → ℂ} {g₀ : Fin 13 → b4b_Group}

theorem b66f_coefficient_relative_extension (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (q : b66f_forms R t 1) :
    ∃ (U : Set (Fin 10 → ℂ)), IsOpen U ∧ t.val ∈ U ∧ U ⊆ b6t_polydisc c₀ ∧
      ∃ θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U,
        ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
          θ.val t ⟨p, w⟩ = q.val a p.val.2 * b66f_gen_b66g_sliceD R t a p w := by
  let M := b66f_gen_b66g_formEquiv R t
  obtain ⟨U, hU, ht, hsub, θ, hθ⟩ := b66f_relative_extension R t (M q)
  refine ⟨U, hU, ht, hsub, θ, ?_⟩
  intro a p hp w
  have he := congrArg (fun φ : b3_HolForm ℂ (b65z_fibre c₀ R.C t) => φ.val ⟨p, w⟩) hθ
  exact he.trans (b66f_gen_b66g_toForm_apply R t q.property a p hp w)


def b66f_gen_b66m_flatPeriod (R : b65z_SharedFamily c₀ g₀) (s : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) :
    (ℂ ⊗[ℤ] b66f_gen_b66g_Homology R s) →ₗ[ℂ] ((Fin 10 → ℂ) → ℂ) :=
  LinearMap.liftBaseChange ℂ
    (b63e_periodFunctionLinear c₀ R.C (b6t_polydisc c₀) (Subset.refl _) R.P θ s)

def b66f_gen_b66m_primitiveHomology (R : b65z_SharedFamily c₀ g₀) (s : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) :
    (ℂ ⊗[ℤ] b60_Lattice) →ₗ[ℂ] (ℂ ⊗[ℤ] b66f_gen_b66g_Homology R s) :=
  letI : Module ℤ (b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
    (Subset.refl _) s) := AddCommGroup.toIntModule _
  let i : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s →ₗ[ℤ] b66f_gen_b66g_Homology R s :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun r x =>
        (int_smul_eq_zsmul (b6m_H1 (b65z_fibre c₀ R.C s)).isModule r x.val).symm }
  (i.baseChange ℂ).comp (b64b_complexMarking _ m).symm.toLinearMap

theorem b66f_gen_b66m_flatPeriod_tmul (R : b65z_SharedFamily c₀ g₀) (s : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (c : ℂ) (x : b66f_gen_b66g_Homology R s) :
    b66f_gen_b66m_flatPeriod R s θ (c ⊗ₜ[ℤ] x) =
      c • b63e_periodFunction c₀ R.C (b6t_polydisc c₀) (Subset.refl _) R.P θ s x := by
  rw [b66f_gen_b66m_flatPeriod, LinearMap.liftBaseChange_tmul]
  rfl

theorem b66f_gen_b66m_flatPeriod_analytic (R : b65z_SharedFamily c₀ g₀) (s : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (hU : IsOpen U) (x : ℂ ⊗[ℤ] b66f_gen_b66g_Homology R s) :
    AnalyticOnNhd ℂ (b66f_gen_b66m_flatPeriod R s θ x) (b6t_polydisc c₀ ∩ U) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    exact analyticOnNhd_const
  | add x y hx hy =>
    rw [map_add]
    exact hx.add hy
  | tmul c x =>
    rw [b66f_gen_b66m_flatPeriod_tmul]
    apply AnalyticOnNhd.const_smul
    exact b63e_period_analytic c₀ R.C (b6t_polydisc c₀) (Subset.refl _)
      (rf5_polydisc_isOpen c₀)
      (fun p => ⟨R.atlas.A p, (R.atlas.hA p).2, (R.atlas.hA p).1, R.atlas.hparam p⟩)
      R.hincl R.P R.hP U hU θ s x

def b66f_gen_b66m_fullTransport (R : b65z_SharedFamily c₀ g₀) (s : b6t_polydisc c₀) (t : b6t_polydisc c₀) :
    b66f_gen_b66g_Homology R s →ₗ[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t) :=
  (R.P t).comp (b6m_H1Equiv (b6m_transport c₀ R.C s t)).toIntLinearEquiv.toLinearMap

theorem b66f_gen_b66m_flatPeriod_transport (R : b65z_SharedFamily c₀ g₀) (s : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (t : b6t_polydisc c₀)
    (x : ℂ ⊗[ℤ] b66f_gen_b66g_Homology R s) :
    b66f_gen_b66m_flatPeriod R s θ x t.val =
      b3_cplxPeriod ℂ (b65z_fibre c₀ R.C t) ((b66f_gen_b66m_fullTransport R s t).baseChange ℂ x)
        (b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _) θ t) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul c x =>
    rw [b66f_gen_b66m_flatPeriod_tmul, LinearMap.baseChange_tmul]
    simp only [Pi.smul_apply, smul_eq_mul, b63e_periodFunction,
      dite_eq_left t.property, b3_cplxPeriod, LinearMap.liftBaseChange_tmul]
    rfl

def b66f_gen_b66m_primitiveFullVector (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) :
    (ℂ ⊗[ℤ] b60_Lattice) →ₗ[ℂ] (ℂ ⊗[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) :=
  ((b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
    (Subset.refl _) R.P s t).baseChange ℂ).comp
      (b64b_complexMarking _ m).symm.toLinearMap

theorem b66f_gen_b66m_primitiveHomology_transport (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (n : ℂ ⊗[ℤ] b60_Lattice) :
    (b66f_gen_b66m_fullTransport R s t).baseChange ℂ (b66f_gen_b66m_primitiveHomology R s m n) =
      b66f_gen_b66m_primitiveFullVector R s t m n := by
  obtain ⟨v, rfl⟩ := (b64b_complexMarking _ m).surjective n
  simp only [b66f_gen_b66m_primitiveHomology, b66f_gen_b66m_primitiveFullVector, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x => rfl

theorem b66f_gen_b66m_primitiveFullVector_mem (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b65z_period R s m t.val)) :
    b66f_gen_b66m_primitiveFullVector R s t m n ∈ b3_periodF ℂ (b65z_fibre c₀ R.C t) := by
  unfold b65z_period at hn
  rw [(b65z_period_chart hg R s m hJ hpol t.val t.property).2, b64c_markedF] at hn
  obtain ⟨v, hv, he⟩ := hn
  have hv' : v ∈ b63e_transportedF c₀ R.C R.hC
      (b6t_polydisc c₀) (Subset.refl _) R.P s t := by
    change v ∈ b65z_transportedFamily R s t.val at hv
    rw [b65z_transportedFamily, dite_eq_left t.property] at hv
    exact hv
  have hn' : (b64b_complexMarking _ m).symm n = v := by
    rw [← he]
    exact (b64b_complexMarking _ m).symm_apply_apply v
  change (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
    (Subset.refl _) R.P s t).baseChange ℂ ((b64b_complexMarking _ m).symm n) ∈ _
  rw [hn']
  exact hv'

theorem b66f_gen_b66m_primitive_flatPeriod_zero (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b65z_period R s m t.val)) :
    b66f_gen_b66m_flatPeriod R s θ (b66f_gen_b66m_primitiveHomology R s m n) t.val = 0 := by
  rw [b66f_gen_b66m_flatPeriod_transport, b66f_gen_b66m_primitiveHomology_transport]
  have he := b66f_gen_b66m_primitiveFullVector_mem hg R s t m hJ hpol n hn
  change b3_cplxPeriod ℂ (b65z_fibre c₀ R.C t)
    (b66f_gen_b66m_primitiveFullVector R s t m n) = 0 at he
  exact congrFun he _

theorem b66f_gen_b66m_normalized_flatPeriod (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (w : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) (n : ℂ ⊗[ℤ] b60_Lattice)
    (hθ : b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _) θ t = w)
    (hw : ∀ x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s,
      (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
        (Subset.refl _) R.P s t x).val w =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n)
    (x : ℂ ⊗[ℤ] b60_Lattice) :
    b66f_gen_b66m_flatPeriod R s θ (b66f_gen_b66m_primitiveHomology R s m x) t.val =
      b60_E.baseChange ℂ x n := by
  rw [b66f_gen_b66m_flatPeriod_transport, b66f_gen_b66m_primitiveHomology_transport, hθ]
  have he := LinearMap.congr_fun (b66f_normalized_periods_complex R s t m w n hw)
    ((b64b_complexMarking _ m).symm x)
  simpa only [b66f_transportPeriods, b66f_gen_b66m_primitiveFullVector, LinearMap.flip_apply,
    LinearMap.comp_apply, LinearMap.codRestrict_apply, b3A_toDual,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.BilinForm.flip_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using he

theorem b66f_gen_b66m_normalized_graph_derivative (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (hU : IsOpen U) (ht : t.val ∈ U)
    (w : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) (i j : Fin 3) (h : Fin 10 → ℂ)
    (hθ : b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _) θ t = w)
    (hw : ∀ x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s,
      (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
        (Subset.refl _) R.P s t x).val w =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
          (b60_frame (b65z_period R s m t.val) (0, i))) :
    fderiv ℂ (b66f_gen_b66m_flatPeriod R s θ (b66f_gen_b66m_primitiveHomology R s m
      (b60_frame (b65z_period R s m t.val) (1, j)))) t.val h =
      (2 / (Complex.I * (Real.sqrt 3 : ℂ))) *
        (fderiv ℂ (b65z_period R s m) t.val h) (finProdFinEquiv (j, i)) := by
  let P := (b66f_gen_b66m_flatPeriod R s θ).comp (b66f_gen_b66m_primitiveHomology R s m)
  have hP (n : ℂ ⊗[ℤ] b60_Lattice) : DifferentiableAt ℂ (P n) t.val :=
    (b66f_gen_b66m_flatPeriod_analytic R s θ hU _ t.val ⟨t.property, ht⟩).differentiableAt
  have hz := (b65z_period_analytic hg R s m hJ hpol t.val t.property).differentiableAt
  have hzero : ∀ᶠ u in 𝓝 t.val, P (b60_frame (b65z_period R s m u) (1, j)) u = 0 := by
    filter_upwards [(rf5_polydisc_isOpen c₀).mem_nhds t.property] with u hu
    exact b66f_gen_b66m_primitive_flatPeriod_zero hg R s ⟨u, hu⟩ m hJ hpol θ _
      (Submodule.subset_span ⟨(1, j), rfl⟩)
  change fderiv ℂ (P (b60_frame (b65z_period R s m t.val) (1, j))) t.val h = _
  rw [b66m_positive_frame_derivative P (b65z_period R s m) t.val h j hP hz hzero]
  have hp (k : Fin 3) : P (b60_eigen 1 (Fin.castAdd 3 k)) t.val =
      if k = i then -(2 / (Complex.I * (Real.sqrt 3 : ℂ))) else 0 := by
    rw [show P (b60_eigen 1 (Fin.castAdd 3 k)) t.val =
        b60_E.baseChange ℂ (b60_eigen 1 (Fin.castAdd 3 k))
          (b60_frame (b65z_period R s m t.val) (0, i)) from
      b66f_gen_b66m_normalized_flatPeriod R s t m θ w _ hθ hw _, b66m_head_pairing]
  simp_rw [hp]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

end HodgeLean.Foundations.Program

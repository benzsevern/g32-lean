import HodgeLean.Foundations.Program.CodifferentialComparisonDirectionProofs
import HodgeLean.Foundations.Program.PathCoverFamilyAnalytic
import HodgeLean.Foundations.Program.CodifferentialComparisonChartProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonDefs


noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful


variable {c₀ : Fin 10 → ℂ} {g₀ : Fin 13 → b4b_Group}

theorem b66f_gen_b66m_transportPeriods_ker (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀) :
    LinearMap.ker (b66f_transportPeriods R s t) =
      b63e_transportedF c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) R.P s t := by
  ext v
  change b66f_transportPeriods R s t v = 0 ↔
    b3_cplxPeriod ℂ (b65z_fibre c₀ R.C t)
      ((b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
        (Subset.refl _) R.P s t).baseChange ℂ v) = 0
  constructor
  · intro h
    funext w
    exact congrArg (fun f : Module.Dual ℂ (b3_HolForm ℂ (b65z_fibre c₀ R.C t)) => f w) h
  · intro h
    ext w
    exact congrFun h w

theorem b66f_gen_b66m_form_of_annihilator (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀)
    (f : Module.Dual ℂ (ℂ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC
      (b6t_polydisc c₀) (Subset.refl _) s))
    (hf : ∀ v, v ∈ b63e_transportedF c₀ R.C R.hC
      (b6t_polydisc c₀) (Subset.refl _) R.P s t → f v = 0) :
    ∃ w : b3_HolForm ℂ (b65z_fibre c₀ R.C t), ∀ v, b66f_transportPeriods R s t v w = f v := by
  letI := b3Forms_holForm_finiteDimensional (C := b65z_fibre c₀ R.C t) (Module.finrank_self ℂ)
  have hm : f ∈ (LinearMap.ker (b66f_transportPeriods R s t)).dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro v hv
    exact hf v (by rwa [b66f_gen_b66m_transportPeriods_ker] at hv)
  rw [LinearMap.dualAnnihilator_ker_eq_range_flip] at hm
  obtain ⟨w, hw⟩ := hm
  exact ⟨w, fun v => LinearMap.congr_fun hw v⟩

theorem b66f_gen_b66m_normalized_holForm (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b65z_period R s m t.val)) :
    ∃ w : b3_HolForm ℂ (b65z_fibre c₀ R.C t),
      ∀ x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s,
        (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
          (Subset.refl _) R.P s t x).val w =
          b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n := by
  let f := ((b60_E.baseChange ℂ).flip n).comp (b64b_complexMarking _ m).toLinearMap
  have hf : ∀ v, v ∈ b63e_transportedF c₀ R.C R.hC
      (b6t_polydisc c₀) (Subset.refl _) R.P s t → f v = 0 := by
    intro v hv
    have hv' : b64b_complexMarking _ m v ∈ b60_F (b65z_period R s m t.val) := by
      unfold b65z_period
      rw [(b65z_period_chart hg R s m hJ hpol t.val t.property).2, b64c_markedF]
      apply Submodule.mem_map_of_mem
      simpa only [b64c_transportedFamily, dite_eq_left t.property] using hv
    exact b60_pairing_F _ _ hv' n hn
  obtain ⟨w, hw⟩ := b66f_gen_b66m_form_of_annihilator R s t f hf
  refine ⟨w, fun x => ?_⟩
  have h := hw (1 ⊗ₜ[ℤ] x)
  simpa only [b66f_transportPeriods, LinearMap.comp_apply, LinearMap.codRestrict_apply,
    b3A_toDual, LinearMap.coe_mk, AddHom.coe_mk, b3_cplxPeriod,
    LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, Pi.smul_apply,
    one_smul, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply,
    AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply, f, LinearEquiv.coe_coe] using h

def b66f_gen_b66m_holProjector (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    b3_HolForm ℂ (b65z_fibre c₀ R.C t) →ₗ[ℂ] b3_HolForm ℂ (b65z_fibre c₀ R.C t) :=
  ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4cov_tau (R.hG t) g⁻¹

def b66f_gen_b66g_formEquiv (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    b66f_forms R t 1 ≃ₗ[ℂ] b3_HolForm ℂ (b65z_fibre c₀ R.C t) where
  toFun q := ⟨b66f_gen_b66g_toForm R t q.val, b66f_gen_b66g_toForm_mem R t q.property⟩
  map_add' q r := Subtype.ext (map_add (b66f_gen_b66g_toForm R t) q.val r.val)
  map_smul' c q := Subtype.ext (map_smul (b66f_gen_b66g_toForm R t) c q.val)
  invFun θ := ⟨b66f_gen_b66g_ofForm R t θ.val, b66f_gen_b66g_ofForm_mem R t θ.property⟩
  left_inv q := Subtype.ext (b66f_gen_b66g_ofForm_toForm R t q.property)
  right_inv θ := Subtype.ext (b66f_gen_b66g_toForm_ofForm R t θ.property.2)

theorem b66f_gen_b66g_projector_apply (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : b66f_Coeff R) (a : b66f_Index R) (x : R.C) :
    b66f_projector R t q a x =
      ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) * b66f_pull R t 1 g q a x := by
  unfold b66f_projector
  rw [LinearMap.sum_apply, Finset.sum_apply, Finset.sum_apply]
  rfl

theorem b66f_gen_b66g_projector_form (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t 1) :
    (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
      b3_pullback ℂ ℂ (fun x : b65z_fibre c₀ R.C t => g • x) (b66f_gen_b66g_toForm R t q)) ∈
        b3_HolForm ℂ (b65z_fibre c₀ R.C t) ∧
    b66f_gen_b66g_ofForm R t (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
      b3_pullback ℂ ℂ (fun x : b65z_fibre c₀ R.C t => g • x) (b66f_gen_b66g_toForm R t q)) =
        b66f_projector R t q := by
  have hmem : (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
      b3_pullback ℂ ℂ (fun x : b65z_fibre c₀ R.C t => g • x) (b66f_gen_b66g_toForm R t q)) ∈
        b3_HolForm ℂ (b65z_fibre c₀ R.C t) :=
    Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _
      (b3_pullback_mem_holForm _ (R.hG t g) _ (b66f_gen_b66g_toForm_mem R t hq))
  refine ⟨hmem, ?_⟩
  funext a x
  rw [b66f_gen_b66g_projector_apply]
  unfold b66f_gen_b66g_ofForm
  split_ifs with h
  · rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    have hap := b66f_gen_b66g_pullback_apply R t q g a ⟨(t, x), rfl⟩ h
      ((b66f_gen_b66g_sliceD R t a ⟨(t, x), rfl⟩ 1)⁻¹)
    have hne := b66f_gen_b66g_slice_ne R t a ⟨(t, x), rfl⟩ h
    rw [hap, b66f_gen_b66g_clm_apply (b66f_gen_b66g_sliceD R t a ⟨(t, x), rfl⟩)]
    change _ * (b66f_pull R t 1 g q a x * _) = _
    field_simp
  · symm
    refine Finset.sum_eq_zero fun g _ => ?_
    change _ * (if (t, x) ∈ (R.atlas.A a).source then _ else 0) = 0
    rw [ite_eq_right h, mul_zero]

theorem b66f_gen_b66g_formEquiv_projector (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : b66f_forms R t 1) :
    ((b66f_gen_b66g_formEquiv R t).symm
      ((∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4_formRepresentation (R.hG t) g)
        (b66f_gen_b66g_formEquiv R t q))).val = b66f_projector R t q.val := by
  rw [← (b66f_gen_b66g_projector_form R t q.property).2]
  change b66f_gen_b66g_ofForm R t _ = b66f_gen_b66g_ofForm R t _
  congr 1
  rw [LinearMap.sum_apply, Submodule.coe_sum]
  have hre := Equiv.sum_comp (Equiv.inv b4b_Group) (fun g => (b4b_projectorCoeff g⁻¹ : ℂ) •
    b3_pullback ℂ ℂ (fun x : b65z_fibre c₀ R.C t => g • x) (b66f_gen_b66g_toForm R t q.val))
  simp only [Equiv.inv_apply, inv_inv] at hre
  refine Eq.trans ?_ (hre.trans (Finset.sum_congr rfl fun g _ => by
    rw [b63l_projectorCoeff_inverse]))
  exact Finset.sum_congr rfl fun g _ => rfl

theorem b66f_gen_b66g_homG_top (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ b4b_Group V) :
    Module.finrank ℂ (b4_HomG ρ (fun g => b4_formRepresentation (R.hG t) g) ⊤) =
      Module.finrank ℂ (b4_HomG ρ (fun g => b4_formAct ℂ (C := b65z_fibre c₀ R.C t) g)
        (b3_HolForm ℂ (b65z_fibre c₀ R.C t))) := by
  let e : b4_HomG ρ (fun g => b4_formRepresentation (R.hG t) g) ⊤ ≃ₗ[ℂ]
      Representation.IntertwiningMap ρ (b4_formRepresentation (R.hG t)) :=
    { toFun := fun φ => (φ.val).intertwiningMap_of_isIntertwiningMap ρ _ φ.2.2
      invFun := fun ψ => ⟨ψ.toLinearMap, fun _ => trivial, fun g v =>
        LinearMap.congr_fun (ψ.isIntertwining' g) v⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, (b4_homGFormEquiv (R.hG t) ρ).finrank_eq]

theorem b66f_gen_b66g_primitive_finrank (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    haveI : FiniteDimensional ℂ (b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :=
      b3Forms_holForm_finiteDimensional (Module.finrank_self ℂ)
    Module.finrank ℂ ((⊤ : Submodule ℂ (b3_HolForm ℂ (b65z_fibre c₀ R.C t))).map
      (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4_formRepresentation (R.hG t) g)) = 6 := by
  letI : FiniteDimensional ℂ (b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :=
    b3Forms_holForm_finiteDimensional (Module.finrank_self ℂ)
  have hm := b65z_period_multiplicities hg R t
  rw [b4_hodge_eq_holo (by simp) (R.hG t),
    b4_hodge_eq_holo (by simp) (R.hG t)] at hm
  rw [b63d_finrank_primitive_image (b4_formRepresentation (R.hG t)) ⊤ (fun _ => le_top),
    b66f_gen_b66g_homG_top, b66f_gen_b66g_homG_top, hm.1, hm.2]


theorem b66f_gen_b66g_primitiveForms_finrank (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    Module.finrank ℂ (b66f_primitiveForms R t) = 6 := by
  have : FiniteDimensional ℂ (b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :=
    b3Forms_holForm_finiteDimensional (Module.finrank_self ℂ)
  set P := ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4_formRepresentation (R.hG t) g
  set M := b66f_gen_b66g_formEquiv R t
  let f := (b66f_forms R t 1).subtype ∘ₗ M.symm.toLinearMap
  have hf : Function.Injective f :=
    (b66f_forms R t 1).injective_subtype.comp M.symm.injective
  have hrange : LinearMap.range ((b66f_projector R t).comp (b66f_forms R t 1).subtype) =
      (LinearMap.range P).map f := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨P (M q), ⟨M q, rfl⟩, b66f_gen_b66g_formEquiv_projector R t q⟩
    · rintro ⟨θ, ⟨θ', rfl⟩, rfl⟩
      refine ⟨M.symm θ', ?_⟩
      change b66f_projector R t (M.symm θ').val = (M.symm (P θ')).val
      rw [← b66f_gen_b66g_formEquiv_projector R t (M.symm θ'), LinearEquiv.apply_symm_apply]
  have hle : LinearMap.range ((b66f_projector R t).comp (b66f_forms R t 1).subtype) ≤
      b66f_forms R t 1 := by
    rw [hrange]
    rintro x ⟨θ, _, rfl⟩
    exact (M.symm θ).property
  have hprim : b66f_primitiveForms R t =
      LinearMap.range ((b66f_projector R t).comp (b66f_forms R t 1).subtype) :=
    inf_eq_right.mpr hle
  rw [hprim, hrange, ← (Submodule.equivMapOfInjective f hf _).finrank_eq, ← Submodule.map_top]
  exact b66f_gen_b66g_primitive_finrank hg R t

theorem b66f_gen_b66g_primitive_comparison_aux (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    (∃ M : b66f_forms R t 1 ≃ₗ[ℂ] b3_HolForm ℂ (b65z_fibre c₀ R.C t),
      (∀ (q : b66f_forms R t 1) (a : b66f_Index R) (p : b65z_fibre c₀ R.C t),
        p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
        (M q).val ⟨p, v⟩ = q.val a p.val.2 *
          (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
            (fun y : b65z_fibre c₀ R.C t => (R.atlas.A a y.val).2) p v)) ∧
      ∀ q : b66f_forms R t 1, ∃ qP : b66f_forms R t 1,
        qP.val = b66f_projector R t q.val ∧
        (M qP).val = ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
          b3_pullback ℂ ℂ (fun x : b65z_fibre c₀ R.C t => g • x) (M q).val) ∧
    Module.finrank ℂ (b66f_primitiveForms R t) = 6 := by
  refine ⟨⟨b66f_gen_b66g_formEquiv R t, fun q a p hp v => b66f_gen_b66g_toForm_apply R t q.property a p hp v,
    fun q => ?_⟩, b66f_gen_b66g_primitiveForms_finrank hg R t⟩
  obtain ⟨hmem, heq⟩ := b66f_gen_b66g_projector_form R t q.property
  exact ⟨⟨b66f_gen_b66g_ofForm R t _, b66f_gen_b66g_ofForm_mem R t hmem⟩, heq, b66f_gen_b66g_toForm_ofForm R t hmem.2⟩

theorem b66f_gen_b66g_primitive_comparison (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    (∃ M : b66f_forms R t 1 ≃ₗ[ℂ] b3_HolForm ℂ (b65z_fibre c₀ R.C t),
      (∀ (q : b66f_forms R t 1) (a : b66f_Index R) (p : b65z_fibre c₀ R.C t),
        p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
        (M q).val ⟨p, v⟩ = q.val a p.val.2 *
          (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
            (fun y : b65z_fibre c₀ R.C t => (R.atlas.A a y.val).2) p v)) ∧
      ∀ q : b66f_forms R t 1, ∃ qP : b66f_forms R t 1,
        qP.val = b66f_projector R t q.val ∧
        (M qP).val = ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
          b3_pullback ℂ ℂ (fun x : b65z_fibre c₀ R.C t => g • x) (M q).val) ∧
    Module.finrank ℂ (b66f_primitiveForms R t) = 6 :=
  b66f_gen_b66g_primitive_comparison_aux hg R t

example := @b66f_gen_b66g_primitive_comparison

theorem b66f_gen_b66m_chart_projector (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    ∃ M : b66f_forms R t 1 ≃ₗ[ℂ] b3_HolForm ℂ (b65z_fibre c₀ R.C t),
      (∀ q, (M q).val = b66f_chartForm R t q.val) ∧
      ∀ q, ∃ qP : b66f_forms R t 1,
        qP.val = b66f_projector R t q.val ∧ M qP = b66f_gen_b66m_holProjector R t (M q) := by
  obtain ⟨M, hM, hP⟩ := (b66f_gen_b66g_primitive_comparison hg R t).1
  refine ⟨M, ?_, ?_⟩
  · intro q
    funext p
    have hp : p.1.val = (t, p.1.val.2) := Prod.ext p.1.property rfl
    have ha : p.1.val ∈ (R.atlas.A (t, p.1.val.2)).source := by
      rw [hp]
      exact (R.atlas.hA _).1
    exact hM q _ p.1 ha p.2
  · intro q
    obtain ⟨qP, hqP, hw⟩ := hP q
    refine ⟨qP, hqP, ?_⟩
    apply Subtype.ext
    simpa only [b66f_gen_b66m_holProjector, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul, b4cov_tau, LinearMap.restrict_apply,
      b4_formAct, inv_inv] using hw

theorem b66f_gen_b66m_holProjector_period (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (l : b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) (w : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    l.val (b66f_gen_b66m_holProjector R t w) = (b4_groupEnd ℂ b4b_projectorCoeff l).val w := by
  let ev : b3_periodLattice ℂ (b65z_fibre c₀ R.C t) →ₗ[ℤ] ℂ :=
    { toFun := fun a => a.val w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L := b3A_toDual ⟨l.val, b3A_lattice_mem_linearDual l⟩
  change L (b66f_gen_b66m_holProjector R t w) = ev (b4_groupEnd ℂ b4b_projectorCoeff l)
  simp only [b66f_gen_b66m_holProjector, LinearMap.sum_apply, LinearMap.smul_apply,
    b4_groupEnd, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro g hg
  change (b4b_projectorCoeff g : ℂ) • l.val (b4cov_tau (R.hG t) g⁻¹ w) =
    b4b_projectorCoeff g • (b4_latticeAct ℂ g l).val w
  rw [b4cov_latticeAct_apply (R.hG t) g (b4_latticeAct_isPushforward (R.hG t) g) l w]
  exact Int.cast_smul_eq_zsmul ℂ _ _

theorem b66f_gen_b66m_primitive_eigen (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) t) :
    b63l_fibreOperator c₀ R.C R.hC t x.val = b4b_projectorDenominator • x.val := by
  obtain ⟨P, _⟩ := b6m_period_comparison (b65z_fibre c₀ R.C t)
  letI := b3_periodLattice_finite (E := ℂ) (C := b65z_fibre c₀ R.C t) (Module.finrank_self ℂ)
  letI := b3_periodLattice_free (E := ℂ) (C := b65z_fibre c₀ R.C t)
  let F := b63l_fibreOperator c₀ R.C R.hC t
  obtain ⟨a, ha, y, hy⟩ := x.property
  have hy' : F y = a • x.val := by
    change F y = _ at hy
    exact hy.trans (int_smul_eq_zsmul (b6m_H1 (b65z_fibre c₀ R.C t)).isModule a x.val)
  have hsq : F (F y) = b4b_projectorDenominator • F y := by
    simpa only [F, Int.cast_smul_eq_zsmul] using
      b63l_fibreOperator_sq c₀ R.C R.hC t y
  apply P.injective
  apply smul_right_injective (b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) ha
  change a • P (F x.val) = a • P (b4b_projectorDenominator • x.val)
  rw [← map_zsmul P a (F x.val), ← map_zsmul P a (b4b_projectorDenominator • x.val)]
  congr 1
  calc
    a • F x.val = F (a • x.val) := (map_zsmul F a x.val).symm
    _ = F (F y) := by rw [← hy']
    _ = b4b_projectorDenominator • F y := hsq
    _ = b4b_projectorDenominator • (a • x.val) := by rw [hy']
    _ = a • (b4b_projectorDenominator • x.val) := smul_comm _ _ _

theorem b66f_gen_b66m_primitive_transport_eigen (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀)
    (x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s) :
    b63l_fibreOperator c₀ R.C R.hC t
      (b6m_H1Equiv (b6m_transport c₀ R.C s t) x.val) =
      b4b_projectorDenominator • b6m_H1Equiv (b6m_transport c₀ R.C s t) x.val := by
  obtain ⟨T, hT, _⟩ := (b63l_fibre_image_transport c₀ R.C R.hC s t).2
  simpa only [hT] using b66f_gen_b66m_primitive_eigen R t (T x)

abbrev b66f_gen_b66g_Homology (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :=
  b6m_H1 (b65z_fibre c₀ R.C t)
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    AddCommGroup (b66f_gen_b66g_Homology R t) := inferInstance

theorem b66f_gen_b66m_periodMap_unique (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (P : b66f_gen_b66g_Homology R t →ₗ[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t))
    (hP : ∀ g : b3_SmoothLoop ℂ (b65z_fibre c₀ R.C t),
      P (b6m_loopClass _ g) = b3_latticePeriod ℂ _ g) : R.P t = P := by
  apply LinearMap.ext
  intro x
  obtain ⟨g, rfl⟩ := b6m_smooth_loopClass_surjective (b65z_fibre c₀ R.C t) x
  exact (R.hP t g).trans (hP g).symm

theorem b66f_gen_b66m_period_operator (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (x : b66f_gen_b66g_Homology R t) :
    R.P t (b63l_fibreOperator c₀ R.C R.hC t x) =
      b4_groupEnd ℂ b4b_projectorCoeff (R.P t x) := by
  obtain ⟨P, hP, hcomm, _⟩ :=
    b63l_period_image_comparison (b65z_fibre c₀ R.C t) (R.hG t)
  rw [b66f_gen_b66m_periodMap_unique R t P.toLinearMap hP]
  exact hcomm x

theorem b66f_gen_b66m_transport_period_eigen (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀)
    (x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s) :
    b4_groupEnd ℂ b4b_projectorCoeff
      (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) R.P s t x) =
      b4b_projectorDenominator •
        b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) R.P s t x := by
  let y := b6m_H1Equiv (b6m_transport c₀ R.C s t) x.val
  have he : b63l_fibreOperator c₀ R.C R.hC t y = b4b_projectorDenominator • y :=
    b66f_gen_b66m_primitive_transport_eigen R s t x
  have hp := b66f_gen_b66m_period_operator R t y
  rw [he, map_zsmul] at hp
  exact hp.symm

theorem b66f_gen_b66m_primitive_form_periods (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀)
    (w : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    ∃ (q : b66f_primitiveForms R t) (wP : b3_HolForm ℂ (b65z_fibre c₀ R.C t)),
      wP.val = b66f_chartForm R t q.val ∧
      ∀ x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s,
        (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
          (Subset.refl _) R.P s t x).val wP =
        (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
          (Subset.refl _) R.P s t x).val w := by
  obtain ⟨M, hM, hP⟩ := b66f_gen_b66m_chart_projector hg R t
  let q0 := M.symm w
  obtain ⟨qP, hqP, hwP⟩ := hP q0
  have hp : qP.val ∈ b66f_primitiveForms R t := ⟨qP.property, q0, hqP.symm⟩
  let z : ℂ := (b4b_projectorDenominator : ℂ)⁻¹
  let qF : b66f_forms R t 1 := z • qP
  have hqF : qF.val ∈ b66f_primitiveForms R t :=
    (b66f_primitiveForms R t).smul_mem z hp
  refine ⟨⟨qF.val, hqF⟩, M qF, hM qF, ?_⟩
  intro x
  let l := b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
    (Subset.refl _) R.P s t x
  let L := b3A_toDual ⟨l.val, b3A_lattice_mem_linearDual l⟩
  change L (M (z • qP)) = L w
  rw [map_smul, map_smul, hwP]
  change z • l.val (b66f_gen_b66m_holProjector R t (M q0)) = l.val w
  rw [show M q0 = w from M.apply_symm_apply w, b66f_gen_b66m_holProjector_period]
  rw [b66f_gen_b66m_transport_period_eigen R s t x]
  change z • (b4b_projectorDenominator • l.val w) = l.val w
  rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  have hd : (b4b_projectorDenominator : ℂ) ≠ 0 := by
    norm_num [b4b_projectorDenominator]
  rw [show z * (b4b_projectorDenominator : ℂ) = 1 from inv_mul_cancel₀ hd, one_smul]

theorem b66f_gen_b66m_normalized_primitiveForm (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b65z_period R s m t.val)) :
    ∃ (q : b66f_primitiveForms R t) (w : b3_HolForm ℂ (b65z_fibre c₀ R.C t)),
      w.val = b66f_chartForm R t q.val ∧
      ∀ x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s,
        (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
          (Subset.refl _) R.P s t x).val w =
          b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n := by
  obtain ⟨w, hw⟩ := b66f_gen_b66m_normalized_holForm hg R s t m hJ hpol n hn
  obtain ⟨q, wP, hq, hP⟩ := b66f_gen_b66m_primitive_form_periods hg R s t w
  exact ⟨q, wP, hq, fun x => (hP x).trans (hw x)⟩

theorem b66f_gen_b66m_normalized_frames (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    : ∃ (q : Fin 2 × Fin 3 → b66f_primitiveForms R t)
      (w : Fin 2 × Fin 3 → b3_HolForm ℂ (b65z_fibre c₀ R.C t)),
      (∀ ij, (w ij).val = b66f_chartForm R t (q ij).val) ∧
      ∀ (ij : Fin 2 × Fin 3)
        (x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s),
        (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
          (Subset.refl _) R.P s t x).val (w ij) =
          b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
            (b60_frame (b65z_period R s m t.val) ij) := by
  have h (ij : Fin 2 × Fin 3) := b66f_gen_b66m_normalized_primitiveForm hg R s t m hJ hpol
    (b60_frame (b65z_period R s m t.val) ij) (Submodule.subset_span ⟨ij, rfl⟩)
  choose q w hchart hperiod using h
  exact ⟨q, w, hchart, hperiod⟩

theorem b66f_gen_b66m_normalized_frames_independent (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (w : Fin 2 × Fin 3 → b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (hw : ∀ (ij : Fin 2 × Fin 3)
      (x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s),
      (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
        (Subset.refl _) R.P s t x).val (w ij) =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
          (b60_frame (b65z_period R s m t.val) ij)) : LinearIndependent ℂ w := by
  let F := (LinearMap.dualMap (b64b_complexMarking _ m).toLinearMap).comp
    (b60_E.baseChange ℂ).flip
  have hF : Function.Injective F := by
    intro a b hab
    apply b66m_polarization_right_injective
    apply LinearMap.ext
    intro y
    obtain ⟨v, rfl⟩ := (b64b_complexMarking _ m).surjective y
    exact congrArg (fun f => f v) hab
  have hli := (b60_frame_independent (b65z_period R s m t.val)).map' F
    (LinearMap.ker_eq_bot_of_injective hF)
  apply LinearIndependent.of_comp (b66f_transportPeriods R s t).flip
  have heq : (b66f_transportPeriods R s t).flip ∘ w =
      F ∘ b60_frame (b65z_period R s m t.val) := by
    funext ij
    exact b66f_normalized_periods_complex R s t m (w ij) _ (hw ij)
  rw [heq]
  exact hli

theorem b66f_gen_b66m_chart_comparison (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    ∃ M : b66f_forms R t 1 ≃ₗ[ℂ] b3_HolForm ℂ (b65z_fibre c₀ R.C t),
      ∀ q, (M q).val = b66f_chartForm R t q.val := by
  obtain ⟨M, hM, _⟩ := (b66f_gen_b66g_primitive_comparison hg R t).1
  refine ⟨M, ?_⟩
  intro q
  funext p
  have hp : p.1.val = (t, p.1.val.2) := Prod.ext p.1.property rfl
  have ha : p.1.val ∈ (R.atlas.A (t, p.1.val.2)).source := by
    rw [hp]
    exact (R.atlas.hA _).1
  exact hM q _ p.1 ha p.2

theorem b66f_gen_b66m_chart_frames_independent (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : Fin 2 × Fin 3 → b66f_primitiveForms R t)
    (w : Fin 2 × Fin 3 → b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (hc : ∀ ij, (w ij).val = b66f_chartForm R t (q ij).val)
    (hw : LinearIndependent ℂ w) : LinearIndependent ℂ q := by
  obtain ⟨M, hM⟩ := b66f_gen_b66m_chart_comparison hg R t
  let I : b66f_primitiveForms R t →ₗ[ℂ] b66f_forms R t 1 :=
    Submodule.inclusion inf_le_left
  have heq : M.toLinearMap.comp I ∘ q = w := by
    funext ij
    apply Subtype.ext
    exact (hM (I (q ij))).trans (hc ij).symm
  apply LinearIndependent.of_comp (M.toLinearMap.comp I)
  rwa [heq]

theorem b66f_gen_b66m_primitive_frame_span (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : Fin 2 × Fin 3 → b66f_primitiveForms R t) (hq : LinearIndependent ℂ q) :
    Submodule.span ℂ (Set.range q) = ⊤ := by
  apply hq.span_eq_top_of_card_eq_finrank
  rw [(b66f_gen_b66g_primitive_comparison hg R t).2]
  decide

theorem b66f_gen_b66m_normalized_basis (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i))) (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    : ∃ (q : Fin 2 × Fin 3 → b66f_primitiveForms R t)
      (w : Fin 2 × Fin 3 → b3_HolForm ℂ (b65z_fibre c₀ R.C t)),
      (∀ ij, (w ij).val = b66f_chartForm R t (q ij).val) ∧
      LinearIndependent ℂ q ∧
      Submodule.span ℂ (Set.range q) = ⊤ ∧
      ∀ (ij : Fin 2 × Fin 3)
        (x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _) s),
        (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
          (Subset.refl _) R.P s t x).val (w ij) =
          b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
            (b60_frame (b65z_period R s m t.val) ij) := by
  obtain ⟨q, w, hc, hp⟩ := b66f_gen_b66m_normalized_frames hg R s t m hJ hpol
  have hw := b66f_gen_b66m_normalized_frames_independent R s t m w hp
  have hq := b66f_gen_b66m_chart_frames_independent hg R t q w hc hw
  exact ⟨q, w, hc, hq, b66f_gen_b66m_primitive_frame_span hg R t q hq, hp⟩

theorem b66f_direction_change_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (s t : b6t_polydisc c)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _)
        s (D.P s) (D.Q s)).baseChange ℚ x y)
    (k : Fin 2) (q q' : Fin 3 → b66f_primitiveForms D t)
    (hq : ∀ i, (q i).val ∈ b66f_direction D s t m k)
    (hq' : ∀ i, (q' i).val ∈ b66f_direction D s t m k)
    (hli : LinearIndependent ℂ q) (hli' : LinearIndependent ℂ q') :
    ∃ P : Matrix (Fin 3) (Fin 3) ℂ, IsUnit P ∧ q' = b66f_reframe D t q P := by
  obtain ⟨f, w, hc, _, hs, hp⟩ :=
    b66f_gen_b66m_normalized_basis hg D s t m hJ hpol
  let H : b66f_primitiveForms D t →ₗ[ℂ] b3_HolForm ℂ (b65z_fibre c D.C t) :=
    { toFun := fun q => ⟨b66f_gen_b66g_toForm D t q.val,
        b66f_gen_b66g_toForm_mem D t q.property.1⟩
      map_add' := fun q r => Subtype.ext (map_add (b66f_gen_b66g_toForm D t) q.val r.val)
      map_smul' := fun z q => Subtype.ext (map_smul (b66f_gen_b66g_toForm D t) z q.val) }
  have hchart (q : b66f_primitiveForms D t) :
      (H q).val = b66f_chartForm D t q.val := by
    funext p
    have hval : p.1.val = (t, p.1.val.2) := Prod.ext p.1.property rfl
    have ha : p.1.val ∈ (D.atlas.A (t, p.1.val.2)).source := by
      rw [hval]
      exact (D.atlas.hA _).1
    exact b66f_gen_b66g_toForm_apply D t q.property.1 _ p.1 ha p.2
  let F := (b66f_transportPeriods D s t).flip.comp H
  let G := (LinearMap.dualMap (b64b_complexMarking _ m).toLinearMap).comp
    (b60_E.baseChange ℂ).flip
  have hG : Function.Injective G := by
    intro a b hab
    apply b66m_polarization_right_injective
    apply LinearMap.ext
    intro y
    obtain ⟨v, rfl⟩ := (b64b_complexMarking _ m).surjective y
    exact congrArg (fun f => f v) hab
  have hw (ij : Fin 2 × Fin 3) : w ij = H (f ij) := by
    exact Subtype.ext ((hc ij).trans (hchart _).symm)
  have hperiod (ij : Fin 2 × Fin 3) (x) :
      (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x).val (w ij) =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
          (b60_frame (b65z_period D s m t.val) ij) := hp ij x
  have himage : F ∘ f = G ∘ b60_frame (b65z_period D s m t.val) := by
    funext ij
    change (b66f_transportPeriods D s t).flip (H (f ij)) = _
    rw [← hw]
    exact b66f_normalized_periods_complex D s t m (w ij) _ (hperiod ij)
  have hF : Function.Injective F := by
    apply LinearMap.injective_of_linearIndependent hs
    rw [himage]
    exact (b60_frame_independent _).map' G (LinearMap.ker_eq_bot_of_injective hG)
  let e : Fin 3 → Module.Dual ℂ
      (ℂ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) :=
    fun i => G (b60_frame (b65z_period D s m t.val) (k, i))
  have hmem (u : b66f_primitiveForms D t)
      (hu : u.val ∈ b66f_direction D s t m k) : F u ∈ Submodule.span ℂ (Set.range e) := by
    obtain ⟨z, hz, a, ha⟩ := hu
    have hzH : z = H u := Subtype.ext (hz.trans (hchart u).symm)
    let n := ∑ i, a i • b60_frame (b65z_period D s m t.val) (k, i)
    have hn (x) :
        (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x).val z =
          b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n := by
      rw [ha]
      simp only [n, map_sum, map_smul, smul_eq_mul]
    have he : F u = G n := by
      change (b66f_transportPeriods D s t).flip (H u) = _
      rw [← hzH]
      exact b66f_normalized_periods_complex D s t m z n hn
    rw [he]
    change G (∑ i, a i • _) ∈ _
    simp only [map_sum, map_smul]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨P, hP, heq⟩ := b66f_frames_in_three_space F hF e q q'
    (fun i => hmem _ (hq i)) (fun i => hmem _ (hq' i)) hli hli'
  exact ⟨P, hP, funext heq⟩

end HodgeLean.Foundations.Program

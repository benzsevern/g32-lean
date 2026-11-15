import HodgeLean.Foundations.Program.PeriodMultiplicationFunctionalProofs
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLoopRepresentatives

noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

theorem b66m_primitive_griffiths_aux (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (n : ℕ) (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) :
    ∃ E : b66g_H1O R t ≃ₗ[ℂ] ((Fin n → ℂ) ⧸ b66g_periodSubspace R s t B),
      ∀ (U : Set (Fin 10 → ℂ)) (_hU : IsOpen U) (_ht : t.val ∈ U)
      (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
      (q : b66g_primitiveForms R t)
      (_hq : ∀ (a : b66k_Index R) (p : rf8_fibre R.C t),
        p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
        θ.val t ⟨p, v⟩ = q.val a p.val.2 *
          (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
            (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p v)),
      DifferentiableAt ℂ (b66g_periods R s B θ) t.val ∧
      ∀ h : Fin 10 → ℂ, ∃ c : b66g_H1O R t,
        c.val = (b66g_scalarBoundaries R t).mkQ
          (b66g_contract R q.val (b66k_cocycle R t h)) ∧
        E c = (b66g_periodSubspace R s t B).mkQ
          (fderiv ℂ (b66g_periods R s B θ) t.val h) := by
  obtain ⟨E, hE⟩ := b66g_griffiths R s t n B
  refine ⟨E, ?_⟩
  intro U hU ht θ q hq
  exact hE U hU ht θ ⟨q.val, q.property.1⟩ hq

theorem b66m_form_transition (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (m : ℕ) (q : b66g_forms R t m) (a b : b66k_Index R) (x : R.C)
    (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source) :
    q.val a x = b66k_vertical R t a b x ^ m * q.val b x := by
  rcases q with ⟨q, hq⟩
  change q a x = b66k_vertical R t a b x ^ m * q b x
  change q ∈ Submodule.span ℂ _ at hq
  induction hq using Submodule.span_induction with
  | mem q hq => exact hq.2.1 a b x ha hb
  | zero => exact (mul_zero _).symm
  | add q r _ _ hq hr =>
    change q a x + r a x = _ * (q b x + r b x)
    rw [hq, hr, mul_add]
  | smul c q _ hq =>
    change c * q a x = _ * (c * q b x)
    rw [hq]
    ring

theorem b66m_form_analytic (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (m : ℕ) (q : b66g_forms R t m) (a : b66k_Index R) :
    AnalyticOnNhd ℂ (fun z => q.val a ((R.atlas.A a).symm (t.val, z)).2)
      (b66k_domain R t a) := by
  rcases q with ⟨q, hq⟩
  change AnalyticOnNhd ℂ (fun z => q a ((R.atlas.A a).symm (t.val, z)).2) _
  change q ∈ Submodule.span ℂ _ at hq
  induction hq using Submodule.span_induction with
  | mem q hq => exact hq.1 a
  | zero => exact analyticOnNhd_const
  | add q r _ _ hq hr => exact hq.add hr
  | smul c q _ hq => exact analyticOnNhd_const.mul hq

theorem b66m_contraction_class (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : b66k_Cochain R)
    (hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
    (q : b66g_forms R t 1) :
    ∃ c : b66g_H1O R t,
      c.val = (b66g_scalarBoundaries R t).mkQ (b66g_contract R q.val u) := by
  obtain ⟨C, hC⟩ := (b66g_cup R t).1
  let c : b66k_cechH1 R t := ⟨(b66k_boundaries R t).mkQ u, u, hu, rfl⟩
  exact ⟨C c q, hC u hu c rfl q⟩

theorem b66m_tensor_splitting (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : b66k_Cochain R) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hm : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hr : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66k_boundary R t v a b x)
    (q : b66g_forms R t 1) :
    let w := fun a z => q.val a ((R.atlas.A a).symm (t.val, z)).2 * v a z
    (∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (w a) z) ∧
    (∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (w a) z) ∧
    ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66g_contract R q.val u a b x = b66g_scalarBoundary R t w a b x := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro a z hz
    exact ((b66m_form_analytic R t 1 q a) z hz).meromorphicAt.mul (hm a z hz)
  · intro a z hz hx
    exact ((b66m_form_analytic R t 1 q a) z hz).mul (hr a z hz hx)
  · intro a b x hx ha hb
    have hpa : (t.val, (R.atlas.A a (t, x)).2) = R.atlas.A a (t, x) :=
      Prod.ext (R.atlas.hparam a (t, x) ha).symm rfl
    have hpb : (t.val, (R.atlas.A b (t, x)).2) = R.atlas.A b (t, x) :=
      Prod.ext (R.atlas.hparam b (t, x) hb).symm rfl
    simp only [b66g_contract, hv a b x hx ha hb, b66k_boundary,
      b66g_scalarBoundary, Set.mem_inter_iff, ha, hb, and_self, ite_true,
      hpa, hpb, (R.atlas.A a).left_inv ha, (R.atlas.A b).left_inv hb]
    have ht := b66m_form_transition R t 1 q a b x ha hb
    rw [pow_one] at ht
    rw [ht]
    ring

theorem b66m_tensor_residue (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ) (q r : b66g_Coeff R) :
    b66g_residueSum R t S
      (fun a z => q a ((R.atlas.A a).symm (t.val, z)).2 * v a z) r =
      b66g_residueSum R t S v (b66g_product R q r) := by
  unfold b66g_residueSum
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  funext z
  simp only [b66g_product]
  ring

attribute [local instance] b3Forms_isManifold_real

open scoped ContDiff in
theorem b66m_principal_pairing_surjective
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (D : C →₀ ℤ)
    (hD : LinearMap.ker (RiemannRochAna_holPrincipalResidueLinear
      (Module.finrank_self ℂ) D) = ⊥) :
    Function.Surjective (RiemannRochAna_principalResidueLinear
      (Module.finrank_self ℂ) D) := by
  letI := b3Forms_holForm_finiteDimensional (C := C) (Module.finrank_self ℂ)
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have hr := RiemannRochAna_principalResidue_rank_add_holKernel (Module.finrank_self ℂ) D
  rw [hD, finrank_bot, add_zero] at hr
  simpa only [Subspace.dual_finrank_eq] using hr

open scoped ContDiff in
theorem b66m_principal_dual_presentation
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (x₀ : C) :
    ∃ m : ℕ,
      Function.Surjective (RiemannRochAna_principalClassLinear
        (Module.finrank_self ℂ) (Finsupp.single x₀ (m : ℤ))) ∧
      Function.Surjective (RiemannRochAna_principalResidueLinear
        (Module.finrank_self ℂ) (Finsupp.single x₀ (m : ℤ))) := by
  have hE := Module.finrank_self ℂ
  obtain ⟨m, hm⟩ := RiemannRochAna_exists_single_holResidueKernel_bot (C := C) hE x₀
  have hg := b66m_principal_pairing_surjective _ hm
  refine ⟨m, ?_, hg⟩
  let D : C →₀ ℤ := Finsupp.single x₀ (m : ℤ)
  have hD : ∀ y, 0 ≤ D y := by
    intro y
    simp only [D, Finsupp.single_apply]
    split_ifs <;> positivity
  letI := (b4c_dolbeault_finite_aux (E := ℂ) (C := C) hE).1
  have h1 := RiemannRochAna_principalResidue_rank_add_holKernel (C := C) hE D
  rw [hm, finrank_bot, add_zero] at h1
  have hk := RiemannRochAna_principalClass_kernel_eq_residueKernel_effective hE D hD x₀
  have hc := (RiemannRochAna_principalClassLinear hE D).finrank_range_add_finrank_ker
  have hr := (RiemannRochAna_principalResidueLinear hE D).finrank_range_add_finrank_ker
  rw [hk] at hc
  change Function.Surjective (RiemannRochAna_principalClassLinear hE D)
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [(b4c_dolbeault_finite_aux (E := ℂ) (C := C) hE).2]
  omega

open scoped ContDiff in
theorem b66m_dolbeault_duality
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (x₀ : C) :
    ∃ (m : ℕ) (J : b4c_Dolbeault01 ℂ C ≃ₗ[ℂ] Module.Dual ℂ (b3_HolForm ℂ C)),
      Function.Surjective (RiemannRochAna_principalClassLinear (Module.finrank_self ℂ)
        (Finsupp.single x₀ (m : ℤ))) ∧
      ∀ c : RiemannRochAna_PrincipalData (Finsupp.single x₀ (m : ℤ)),
        J (RiemannRochAna_principalClassLinear (Module.finrank_self ℂ)
          (Finsupp.single x₀ (m : ℤ)) c) =
        RiemannRochAna_principalResidueLinear (Module.finrank_self ℂ)
          (Finsupp.single x₀ (m : ℤ)) c := by
  obtain ⟨m, hf, hg⟩ := b66m_principal_dual_presentation x₀
  let D : C →₀ ℤ := Finsupp.single x₀ (m : ℤ)
  let f := RiemannRochAna_principalClassLinear (Module.finrank_self ℂ) D
  let g := RiemannRochAna_principalResidueLinear (Module.finrank_self ℂ) D
  have hD : ∀ y, 0 ≤ D y := by
    intro y
    simp only [D, Finsupp.single_apply]
    split_ifs <;> positivity
  have hk : LinearMap.ker f = LinearMap.ker g :=
    RiemannRochAna_principalClass_kernel_eq_residueKernel_effective
      (Module.finrank_self ℂ) D hD x₀
  let J := f.liftOfSurjective hf ⟨g, hk.le⟩
  have hJ (c) : J (f c) = g c := LinearMap.equivOfSurjective_apply hf hk.le
  have hi : Function.Injective J := by
    intro x y hxy
    obtain ⟨c, rfl⟩ := hf x
    obtain ⟨d, rfl⟩ := hf y
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply LinearMap.mem_ker.mp
    rw [hk]
    change g (c - d) = 0
    rw [map_sub, ← hJ, ← hJ, hxy, sub_self]
  have hs : Function.Surjective J := by
    intro l
    obtain ⟨c, hc⟩ := hg l
    exact ⟨f c, (hJ c).trans hc⟩
  exact ⟨m, LinearEquiv.ofBijective J ⟨hi, hs⟩, hf, hJ⟩

open scoped ContDiff in
theorem b66m_principal_pairing_extension
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (D₀ : C →₀ ℤ) (h₀ : ∀ x, 0 ≤ D₀ x)
    (hf : Function.Surjective (RiemannRochAna_principalClassLinear (Module.finrank_self ℂ) D₀))
    (J : b4c_Dolbeault01 ℂ C →ₗ[ℂ] Module.Dual ℂ (b3_HolForm ℂ C))
    (hJ : ∀ c, J (RiemannRochAna_principalClassLinear (Module.finrank_self ℂ) D₀ c) =
      RiemannRochAna_principalResidueLinear (Module.finrank_self ℂ) D₀ c)
    (D : C →₀ ℤ) (hD : ∀ x, 0 ≤ D x) (c : RiemannRochAna_PrincipalData D) :
    J (RiemannRochAna_principalClassLinear (Module.finrank_self ℂ) D c) =
      RiemannRochAna_principalResidueLinear (Module.finrank_self ℂ) D c := by
  have hE := Module.finrank_self ℂ
  let B := D₀ + D
  have h₀B : ∀ x, D₀ x ≤ B x := fun x => by
    dsimp [B]
    exact le_add_of_nonneg_right (hD x)
  have hDB : ∀ x, D x ≤ B x := fun x => by
    dsimp [B]
    exact le_add_of_nonneg_left (h₀ x)
  obtain ⟨d, hd⟩ := hf (RiemannRochAna_principalClassLinear hE D c)
  let e₀ := RiemannRochAna_principalDataExtend D₀ B d
  let e := RiemannRochAna_principalDataExtend D B c
  have hc : RiemannRochAna_principalClassLinear hE B (e₀ - e) = 0 := by
    rw [map_sub, ← RiemannRochAna_principalDataExtend_class hE D₀ B h₀ h₀B d,
      ← RiemannRochAna_principalDataExtend_class hE D B hD hDB c, hd, sub_self]
  have hr : RiemannRochAna_principalResidueLinear hE B (e₀ - e) = 0 :=
    LinearMap.mem_ker.mp
      (RiemannRochAna_principalClass_kernel_le_residueKernel hE B (LinearMap.mem_ker.mpr hc))
  rw [map_sub] at hr
  ext θ
  have ht := congrArg (fun l : Module.Dual ℂ (b3_HolForm ℂ C) => l θ) hr
  change RiemannRochAna_principalResiduePairing hE B e₀ θ -
    RiemannRochAna_principalResiduePairing hE B e θ = 0 at ht
  rw [RiemannRochAna_principalDataExtend_residuePairing hE D₀ B h₀ h₀B d θ,
    RiemannRochAna_principalDataExtend_residuePairing hE D B hD hDB c θ] at ht
  rw [← hd, hJ]
  exact sub_eq_zero.mp ht

open scoped ContDiff in
theorem b66m_dolbeault_serre
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (x₀ : C) :
    ∃ J : b4c_Dolbeault01 ℂ C ≃ₗ[ℂ] Module.Dual ℂ (b3_HolForm ℂ C),
      ∀ (D : C →₀ ℤ) (_hD : ∀ x, 0 ≤ D x) (c : RiemannRochAna_PrincipalData D),
        J (RiemannRochAna_principalClassLinear (Module.finrank_self ℂ) D c) =
          RiemannRochAna_principalResidueLinear (Module.finrank_self ℂ) D c := by
  obtain ⟨m, J, hf, hJ⟩ := b66m_dolbeault_duality x₀
  have h₀ : ∀ y, 0 ≤ (Finsupp.single x₀ (m : ℤ)) y := by
    intro y
    simp only [Finsupp.single_apply]
    split_ifs <;> positivity
  exact ⟨J, fun D hD c => b66m_principal_pairing_extension _ h₀ hf
    J.toLinearMap hJ D hD c⟩

theorem b66m_scalar_duality (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Nonempty (b66g_H1O R t ≃ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 1)) := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℂ))
    (M := rf8_fibre R.C t) isClosed_univ
    (fun c => {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A c).source})
    (fun c => b66m_sc_open_source R t c)
    (fun y _ => mem_iUnion.mpr ⟨y.val, (R.atlas.hA y.val).1⟩)
  obtain ⟨E, _⟩ := b66m_sc_comparison_equiv R t ρ hρ
  obtain ⟨M, _, _⟩ := (b66g_primitive_comparison R t).1
  obtain ⟨x⟩ : Nonempty (rf8_fibre R.C t) := inferInstance
  obtain ⟨J, _⟩ := b66m_dolbeault_serre x
  exact ⟨E.trans (J.trans M.dualMap)⟩

def b66m_multiplyLinear (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_forms R t 1) : b66g_forms R t 1 →ₗ[ℂ] b66g_forms R t 2 where
  toFun r := ⟨b66g_product R q.val r.val, (b66g_cup R t).2 q r⟩
  map_add' r s := by
    apply Subtype.ext
    funext a x
    exact mul_add _ _ _
  map_smul' c r := by
    apply Subtype.ext
    funext a x
    change q.val a x * (c * r.val a x) = c * (q.val a x * r.val a x)
    ring

theorem b66m_multiplyLinear_injective (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_forms R t 1) (hq : q.val ≠ 0) :
    Function.Injective (b66m_multiplyLinear R t q) := by
  intro r s hrs
  apply sub_eq_zero.mp
  apply Subtype.ext
  by_contra hn
  apply b66m_rs_product_ne_zero R t q.property (r - s).property hq hn
  have hz : b66m_multiplyLinear R t q (r - s) = 0 := by
    rw [map_sub, hrs, sub_self]
  exact congrArg Subtype.val hz

def b66m_residuePairing (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66g_H1O R t →ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 1) :=
  Classical.choose (b66m_rs_serre_functional R t)

theorem b66m_residuePairing_contract (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : b66k_Cochain R)
    (hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hm : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hr : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66k_boundary R t v a b x)
    (q : b66g_forms R t 1) :
    ∃ c : b66g_H1O R t,
      c.val = (b66g_scalarBoundaries R t).mkQ (b66g_contract R q.val u) ∧
      ∀ r : b66g_forms R t 1, b66m_residuePairing R t c r =
        b66g_residueSum R t S v (b66g_product R q.val r.val) := by
  have hcycles := b66m_rs_contract_mem R t q.property hu
  let c : b66g_H1O R t :=
    ⟨(b66g_scalarBoundaries R t).mkQ (b66g_contract R q.val u),
      b66g_contract R q.val u, hcycles, rfl⟩
  obtain ⟨hm', hr', hv'⟩ := b66m_tensor_splitting R t u S v hm hr hv q
  refine ⟨c, rfl, fun r => ?_⟩
  have he := Classical.choose_spec (b66m_rs_serre_functional R t)
    (b66g_contract R q.val u) hcycles c rfl S
    (fun a z => q.val a ((R.atlas.A a).symm (t.val, z)).2 * v a z) hm' hr' hv' r
  exact he.trans (b66m_tensor_residue R t S v q.val r.val)

theorem b66m_residuePairing_surjective (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Function.Surjective (b66m_residuePairing R t) := by
  obtain ⟨q, hq, hq0⟩ := b66m_rs_form_exists R t
  let Q : b66g_forms R t 1 := ⟨q, hq⟩
  let M := b66m_multiplyLinear R t Q
  have hM : Function.Injective M := b66m_multiplyLinear_injective R t Q hq0
  obtain ⟨E, hE⟩ := b66g_serre_pairing R t
  intro l
  obtain ⟨f, hf⟩ := LinearMap.dualMap_surjective_of_injective hM l
  let cu := E.symm f
  obtain ⟨u, hu, hcu⟩ := cu.property
  obtain ⟨S, v, hm, hr, hv⟩ := b66g_meromorphic_splitting R t u hu
  obtain ⟨c, hc, hΦ⟩ := b66m_residuePairing_contract R t u hu S v hm hr hv Q
  refine ⟨c, ?_⟩
  ext r
  have he := hE u hu cu hcu.symm S v hm hr hv (M r)
  calc
    b66m_residuePairing R t c r =
        b66g_residueSum R t S v (b66g_product R Q.val r.val) := hΦ r
    _ = (E cu) (M r) := he.symm
    _ = f (M r) := by
      change (E (E.symm f)) (M r) = f (M r)
      rw [E.apply_symm_apply]
    _ = l r := congrArg (fun k : Module.Dual ℂ (b66g_forms R t 1) => k r) hf

theorem b66m_dual_contraction_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ J : b66g_H1O R t ≃ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 1),
      ∀ (u : b66k_Cochain R)
      (_hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
      (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
      (_hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
      (_hreg : ∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
      (_hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source → u a b x = b66k_boundary R t v a b x)
      (q r : b66g_forms R t 1),
      ∃ c : b66g_H1O R t,
        c.val = (b66g_scalarBoundaries R t).mkQ (b66g_contract R q.val u) ∧
        J c r = b66g_residueSum R t S v (b66g_product R q.val r.val) := by
  obtain ⟨F⟩ := b66m_scalar_duality R t
  letI := (b66m_sc_finite R t).1
  letI : Module.Finite ℂ (Module.Dual ℂ (b66g_forms R t 1)) :=
    Module.Finite.of_injective F.symm.toLinearMap F.symm.injective
  have hs := b66m_residuePairing_surjective R t
  have hi : Function.Injective (b66m_residuePairing R t) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank F.finrank_eq).mpr hs
  refine ⟨LinearEquiv.ofBijective (b66m_residuePairing R t) ⟨hi, hs⟩, ?_⟩
  intro u hu S v hm hr hv q r
  obtain ⟨c, hc, hΦ⟩ := b66m_residuePairing_contract R t u hu S v hm hr hv q
  exact ⟨c, hc, hΦ r⟩

theorem b66m_symmetric_product_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : b66g_primitiveForms R t) :
    b66m_multiply R t q r = b66m_multiply R t r q ∧
    b66m_multiply R t q r ∈ b66g_forms R t 2 ∧
    ∀ g : b4b_Group, b66g_pull R t 2 g (b66m_multiply R t q r) =
      b66m_multiply R t q r := by
  obtain ⟨S, v, hm, hr, hv⟩ := b66g_meromorphic_splitting R t
    (b66k_cocycle R t 0) (b66k_cocycle_mem R t 0)
  obtain ⟨Q, hQ, hi, _⟩ := b66g_invariant_primitive R t 0 S v hm hr hv q r
  refine ⟨?_, ?_, ?_⟩
  · unfold b66m_multiply
    congr 1
    funext a x
    exact mul_comm _ _
  · change b66g_average R t (b66g_product R q.val r.val) ∈ _
    rw [← hQ]
    exact Q.property
  · change ∀ g, b66g_pull R t 2 g
      (b66g_average R t (b66g_product R q.val r.val)) =
        b66g_average R t (b66g_product R q.val r.val)
    rw [← hQ]
    exact hi

theorem b66m_residue_matrix_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : Fin 3 → b66g_primitiveForms R t)
    (S S' : Fin 10 → Finset R.C)
    (v v' : Fin 10 → b66k_Index R → ℂ → ℂ)
    (hmero : ∀ j a z, z ∈ b66k_domain R t a → MeromorphicAt (v j a) z)
    (hreg : ∀ j a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z)
    (hv : ∀ j a b x, x ∉ S j → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t (Pi.single j 1) a b x = b66k_boundary R t (v j) a b x)
    (hmero' : ∀ j a z, z ∈ b66k_domain R t a → MeromorphicAt (v' j a) z)
    (hreg' : ∀ j a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S' j → AnalyticAt ℂ (v' j a) z)
    (hv' : ∀ j a b x, x ∉ S' j → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t (Pi.single j 1) a b x = b66k_boundary R t (v' j) a b x) :
    b66m_multiplicationMatrix R t q r S v = b66m_multiplicationMatrix R t q r S' v' ∧
    ∀ i j, b66m_multiplicationMatrix R t q r S v i j =
      b66g_residueSum R t (S j) (v j)
        (b66g_product R (q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1).val
          (r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2).val) := by
  obtain ⟨E, hE⟩ := b66g_serre_pairing R t
  constructor
  · funext i j
    let q₀ := q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1
    let r₀ := r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2
    let Q : b66g_forms R t 2 :=
      ⟨b66m_multiply R t q₀ r₀, (b66m_symmetric_product_aux R t q₀ r₀).2.1⟩
    let u := b66k_cocycle R t (Pi.single j 1)
    have hu := b66k_cocycle_mem R t (Pi.single j 1)
    let c : b66k_cechH1 R t := ⟨(b66k_boundaries R t).mkQ u, u, hu, rfl⟩
    exact (hE u hu c rfl (S j) (v j) (hmero j) (hreg j) (hv j) Q).symm.trans
      (hE u hu c rfl (S' j) (v' j) (hmero' j) (hreg' j) (hv' j) Q)
  · intro i j
    obtain ⟨Q, hQ, _, he⟩ := b66g_invariant_primitive R t (Pi.single j 1)
      (S j) (v j) (hmero j) (hreg j) (hv j)
      (q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1)
      (r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2)
    change b66g_residueSum R t (S j) (v j)
      (b66g_average R t (b66g_product R _ _)) = _
    rw [← hQ]
    exact he

theorem b66m_tail_pairing (z : Fin 9 → ℂ) (k j : Fin 3) :
    b60_E.baseChange ℂ (b60c_eigenBasis (0, Fin.natAdd 3 k))
      (b60_frame z (1, j)) =
        if k = j then -(2 / (Complex.I * (Real.sqrt 3 : ℂ))) else 0 := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hnorm : ((Real.sqrt 2 : ℂ) ^ 2)⁻¹ = 1 / 2 := by rw [hsq]; norm_num
  fin_cases k <;> fin_cases j <;>
    simp [b60c_eigenBasis_apply, b60_frame, b60_pairing_eigen,
      Fin.sum_univ_succ, b60_diag, hnorm] <;> ring

theorem b66m_leftMatrix_permutation (z : Fin 9 → ℂ) (κ : ℂ) :
    b66m_leftMatrix z κ =
      (-(κ * (2 / (Complex.I * (Real.sqrt 3 : ℂ))))) •
        (Equiv.Perm.permMatrix ℂ
          ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm.trans
            ((Equiv.prodComm (Fin 3) (Fin 3)).trans finProdFinEquiv))) := by
  ext a b
  simp only [b66m_leftMatrix, b66m_tail_pairing, Matrix.smul_apply,
    smul_eq_mul, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap]
  have hab : b = finProdFinEquiv
      (((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).2,
        ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).1) ↔
      ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm b).1 =
        ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).2 ∧
      ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm b).2 =
        ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).1 := by
    rw [← Equiv.symm_apply_eq, Prod.ext_iff]
  by_cases h₁ :
      ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).1 =
        ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm b).2
  · by_cases h₂ :
        ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm b).1 =
          ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).2
    · have he := hab.mpr ⟨h₂, h₁.symm⟩
      rw [ite_eq_left h₁, ite_eq_left h₂, ite_eq_left he.symm, mul_one, mul_neg]
    · have he : b ≠ finProdFinEquiv
          (((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).2,
            ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).1) :=
        fun h => h₂ (hab.mp h).1
      rw [ite_eq_left h₁, ite_eq_right h₂, ite_eq_right (Ne.symm he), mul_zero,
        mul_zero]
  · have he : b ≠ finProdFinEquiv
        (((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).2,
          ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).1) :=
      fun h => h₁ (hab.mp h).2.symm
    rw [ite_eq_right h₁, ite_eq_right (Ne.symm he), mul_zero]

theorem b66m_leftMatrix_isUnit (z : Fin 9 → ℂ) (κ : ℂ) (hk : κ ≠ 0) :
    IsUnit (b66m_leftMatrix z κ) := by
  let σ : Equiv.Perm (Fin 9) :=
    (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm.trans
      ((Equiv.prodComm (Fin 3) (Fin 3)).trans finProdFinEquiv)
  have hσ : IsUnit (σ.permMatrix ℂ) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨(σ⁻¹).permMatrix ℂ, ?_⟩
    rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hc : -(κ * (2 / (Complex.I * (Real.sqrt 3 : ℂ)))) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero hk
      (div_ne_zero (by norm_num) (mul_ne_zero Complex.I_ne_zero hs)))
  have hu := (isUnit_iff_ne_zero.mpr hc).map
    (algebraMap ℂ (Matrix (Fin 9) (Fin 9) ℂ))
  rw [b66m_leftMatrix_permutation]
  simpa only [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, σ]
    using hu.mul hσ

theorem b66m_chart_comparison (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ M : b66g_forms R t 1 ≃ₗ[ℂ] b3_HolForm ℂ (rf8_fibre R.C t),
      ∀ q, (M q).val = b66m_chartForm R t q.val := by
  obtain ⟨M, hM, _⟩ := (b66g_primitive_comparison R t).1
  refine ⟨M, ?_⟩
  intro q
  funext p
  have hp : p.1.val = (t, p.1.val.2) := Prod.ext p.1.property rfl
  have ha : p.1.val ∈ (R.atlas.A (t, p.1.val.2)).source := by
    rw [hp]
    exact (R.atlas.hA _).1
  exact hM q _ p.1 ha p.2

def b66m_transportPeriods (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base) :
    (ℂ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) →ₗ[ℂ] Module.Dual ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) :=
  (b3A_toDual.comp ((b3_cplxPeriod ℂ (rf8_fibre R.C t)).codRestrict
    (b3_linearDual ℂ (rf8_fibre R.C t)) (fun v => b3A_cplxPeriod_mem_linearDual v))).comp
      ((b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) R.P s t).baseChange ℂ)

theorem b66m_transportPeriods_ker (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base) :
    LinearMap.ker (b66m_transportPeriods R s t) =
      b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s t := by
  ext v
  change b66m_transportPeriods R s t v = 0 ↔
    b3_cplxPeriod ℂ (rf8_fibre R.C t)
      ((b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) R.P s t).baseChange ℂ v) = 0
  constructor
  · intro h
    funext w
    exact congrArg (fun f : Module.Dual ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) => f w) h
  · intro h
    ext w
    exact congrFun h w

theorem b66m_form_of_annihilator (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (f : Module.Dual ℂ (ℂ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) s))
    (hf : ∀ v, v ∈ b63e_transportedF mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) R.P s t → f v = 0) :
    ∃ w : b3_HolForm ℂ (rf8_fibre R.C t), ∀ v, b66m_transportPeriods R s t v w = f v := by
  letI := b3Forms_holForm_finiteDimensional (C := rf8_fibre R.C t) (Module.finrank_self ℂ)
  have hm : f ∈ (LinearMap.ker (b66m_transportPeriods R s t)).dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro v hv
    exact hf v (by rwa [b66m_transportPeriods_ker] at hv)
  rw [LinearMap.dualAnnihilator_ker_eq_range_flip] at hm
  obtain ⟨w, hw⟩ := hm
  exact ⟨w, fun v => LinearMap.congr_fun hw v⟩

theorem b66m_normalized_holForm (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b64i_period R s m t.val)) :
    ∃ w : b3_HolForm ℂ (rf8_fibre R.C t),
      ∀ x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s,
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val w =
          b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n := by
  let f := ((b60_E.baseChange ℂ).flip n).comp (b64b_complexMarking _ m).toLinearMap
  have hf : ∀ v, v ∈ b63e_transportedF mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) R.P s t → f v = 0 := by
    intro v hv
    have hv' : b64b_complexMarking _ m v ∈ b60_F (b64i_period R s m t.val) := by
      rw [(b64i_chart R s m hJ hpol t.val t.property).2, b64c_markedF]
      apply Submodule.mem_map_of_mem
      simpa only [rf8_transportedFamily, dite_eq_left t.property] using hv
    exact b60_pairing_F _ _ hv' n hn
  obtain ⟨w, hw⟩ := b66m_form_of_annihilator R s t f hf
  refine ⟨w, fun x => ?_⟩
  have h := hw (1 ⊗ₜ[ℤ] x)
  simpa only [b66m_transportPeriods, LinearMap.comp_apply, LinearMap.codRestrict_apply,
    b3A_toDual, LinearMap.coe_mk, AddHom.coe_mk, b3_cplxPeriod,
    LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, Pi.smul_apply,
    one_smul, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply,
    AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply, f, LinearEquiv.coe_coe] using h

theorem b66m_periodMap_unique (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (P : b66g_Homology R t →ₗ[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t))
    (hP : ∀ g : b3_SmoothLoop ℂ (rf8_fibre R.C t),
      P (b6m_loopClass _ g) = b3_latticePeriod ℂ _ g) : R.P t = P := by
  apply LinearMap.ext
  intro x
  obtain ⟨g, rfl⟩ := b6m_smooth_loopClass_surjective (rf8_fibre R.C t) x
  exact (R.hP t g).trans (hP g).symm

theorem b66m_periodMap_bijective (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Function.Bijective (R.P t) := by
  obtain ⟨P, hP⟩ := b6m_period_comparison (rf8_fibre R.C t)
  rw [b66m_periodMap_unique R t P.toLinearMap hP]
  exact P.bijective

theorem b66m_primitive_eigen (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) t) :
    b63l_fibreOperator mr_base R.C R.hC t x.val = b4b_projectorDenominator • x.val := by
  obtain ⟨P, _⟩ := b6m_period_comparison (rf8_fibre R.C t)
  letI := b3_periodLattice_finite (E := ℂ) (C := rf8_fibre R.C t) (Module.finrank_self ℂ)
  letI := b3_periodLattice_free (E := ℂ) (C := rf8_fibre R.C t)
  let F := b63l_fibreOperator mr_base R.C R.hC t
  obtain ⟨a, ha, y, hy⟩ := x.property
  have hy' : F y = a • x.val := by
    change F y = _ at hy
    exact hy.trans (int_smul_eq_zsmul (b6m_H1 (rf8_fibre R.C t)).isModule a x.val)
  have hsq : F (F y) = b4b_projectorDenominator • F y := by
    simpa only [F, Int.cast_smul_eq_zsmul] using
      b63l_fibreOperator_sq mr_base R.C R.hC t y
  apply P.injective
  apply smul_right_injective (b3_periodLattice ℂ (rf8_fibre R.C t)) ha
  change a • P (F x.val) = a • P (b4b_projectorDenominator • x.val)
  rw [← map_zsmul P a (F x.val), ← map_zsmul P a (b4b_projectorDenominator • x.val)]
  congr 1
  calc
    a • F x.val = F (a • x.val) := (map_zsmul F a x.val).symm
    _ = F (F y) := by rw [← hy']
    _ = b4b_projectorDenominator • F y := hsq
    _ = b4b_projectorDenominator • (a • x.val) := by rw [hy']
    _ = a • (b4b_projectorDenominator • x.val) := smul_comm _ _ _


theorem b66m_primitive_transport_eigen (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s) :
    b63l_fibreOperator mr_base R.C R.hC t
      (b6m_H1Equiv (b6m_transport mr_base R.C s t) x.val) =
      b4b_projectorDenominator • b6m_H1Equiv (b6m_transport mr_base R.C s t) x.val := by
  obtain ⟨T, hT, _⟩ := (b63l_fibre_image_transport mr_base R.C R.hC s t).2
  simpa only [hT] using b66m_primitive_eigen R t (T x)

theorem b66m_period_operator (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (x : b66g_Homology R t) :
    R.P t (b63l_fibreOperator mr_base R.C R.hC t x) =
      b4_groupEnd ℂ b4b_projectorCoeff (R.P t x) := by
  obtain ⟨P, hP, hcomm, _⟩ :=
    b63l_period_image_comparison (rf8_fibre R.C t) (R.hG t)
  rw [b66m_periodMap_unique R t P.toLinearMap hP]
  exact hcomm x

theorem b66m_transport_period_eigen (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s) :
    b4_groupEnd ℂ b4b_projectorCoeff
      (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s t x) =
      b4b_projectorDenominator •
        b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s t x := by
  let y := b6m_H1Equiv (b6m_transport mr_base R.C s t) x.val
  have he : b63l_fibreOperator mr_base R.C R.hC t y = b4b_projectorDenominator • y :=
    b66m_primitive_transport_eigen R s t x
  have hp := b66m_period_operator R t y
  rw [he, map_zsmul] at hp
  exact hp.symm

def b66m_holProjector (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b3_HolForm ℂ (rf8_fibre R.C t) →ₗ[ℂ] b3_HolForm ℂ (rf8_fibre R.C t) :=
  ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4cov_tau (R.hG t) g⁻¹

theorem b66m_holProjector_period (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (l : b3_periodLattice ℂ (rf8_fibre R.C t)) (w : b3_HolForm ℂ (rf8_fibre R.C t)) :
    l.val (b66m_holProjector R t w) = (b4_groupEnd ℂ b4b_projectorCoeff l).val w := by
  let ev : b3_periodLattice ℂ (rf8_fibre R.C t) →ₗ[ℤ] ℂ :=
    { toFun := fun a => a.val w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L := b3A_toDual ⟨l.val, b3A_lattice_mem_linearDual l⟩
  change L (b66m_holProjector R t w) = ev (b4_groupEnd ℂ b4b_projectorCoeff l)
  simp only [b66m_holProjector, LinearMap.sum_apply, LinearMap.smul_apply,
    b4_groupEnd, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro g hg
  change (b4b_projectorCoeff g : ℂ) • l.val (b4cov_tau (R.hG t) g⁻¹ w) =
    b4b_projectorCoeff g • (b4_latticeAct ℂ g l).val w
  rw [b4cov_latticeAct_apply (R.hG t) g (b4_latticeAct_isPushforward (R.hG t) g) l w]
  exact Int.cast_smul_eq_zsmul ℂ _ _

theorem b66m_chart_projector (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ M : b66g_forms R t 1 ≃ₗ[ℂ] b3_HolForm ℂ (rf8_fibre R.C t),
      (∀ q, (M q).val = b66m_chartForm R t q.val) ∧
      ∀ q, ∃ qP : b66g_forms R t 1,
        qP.val = b66g_projector R t q.val ∧ M qP = b66m_holProjector R t (M q) := by
  obtain ⟨M, hM, hP⟩ := (b66g_primitive_comparison R t).1
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
    simpa only [b66m_holProjector, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul, b4cov_tau, LinearMap.restrict_apply,
      b4_formAct, inv_inv] using hw

theorem b66m_primitive_form_periods (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (w : b3_HolForm ℂ (rf8_fibre R.C t)) :
    ∃ (q : b66g_primitiveForms R t) (wP : b3_HolForm ℂ (rf8_fibre R.C t)),
      wP.val = b66m_chartForm R t q.val ∧
      ∀ x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s,
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val wP =
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val w := by
  obtain ⟨M, hM, hP⟩ := b66m_chart_projector R t
  let q0 := M.symm w
  obtain ⟨qP, hqP, hwP⟩ := hP q0
  have hp : qP.val ∈ b66g_primitiveForms R t := ⟨qP.property, q0, hqP.symm⟩
  let z : ℂ := (b4b_projectorDenominator : ℂ)⁻¹
  let qF : b66g_forms R t 1 := z • qP
  have hqF : qF.val ∈ b66g_primitiveForms R t :=
    (b66g_primitiveForms R t).smul_mem z hp
  refine ⟨⟨qF.val, hqF⟩, M qF, hM qF, ?_⟩
  intro x
  let l := b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
    (Subset.refl _) R.P s t x
  let L := b3A_toDual ⟨l.val, b3A_lattice_mem_linearDual l⟩
  change L (M (z • qP)) = L w
  rw [map_smul, map_smul, hwP]
  change z • l.val (b66m_holProjector R t (M q0)) = l.val w
  rw [show M q0 = w from M.apply_symm_apply w, b66m_holProjector_period]
  rw [b66m_transport_period_eigen R s t x]
  change z • (b4b_projectorDenominator • l.val w) = l.val w
  rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  have hd : (b4b_projectorDenominator : ℂ) ≠ 0 := by
    norm_num [b4b_projectorDenominator]
  rw [show z * (b4b_projectorDenominator : ℂ) = 1 from inv_mul_cancel₀ hd, one_smul]

theorem b66m_normalized_primitiveForm (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b64i_period R s m t.val)) :
    ∃ (q : b66g_primitiveForms R t) (w : b3_HolForm ℂ (rf8_fibre R.C t)),
      w.val = b66m_chartForm R t q.val ∧
      ∀ x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s,
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val w =
          b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n := by
  obtain ⟨w, hw⟩ := b66m_normalized_holForm R s t m hJ hpol n hn
  obtain ⟨q, wP, hq, hP⟩ := b66m_primitive_form_periods R s t w
  exact ⟨q, wP, hq, fun x => (hP x).trans (hw x)⟩

theorem b66m_normalized_frames (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    : ∃ (q : Fin 2 × Fin 3 → b66g_primitiveForms R t)
      (w : Fin 2 × Fin 3 → b3_HolForm ℂ (rf8_fibre R.C t)),
      (∀ ij, (w ij).val = b66m_chartForm R t (q ij).val) ∧
      ∀ (ij : Fin 2 × Fin 3)
        (x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s),
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val (w ij) =
          b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
            (b60_frame (b64i_period R s m t.val) ij) := by
  have h (ij : Fin 2 × Fin 3) := b66m_normalized_primitiveForm R s t m hJ hpol
    (b60_frame (b64i_period R s m t.val) ij) (Submodule.subset_span ⟨ij, rfl⟩)
  choose q w hchart hperiod using h
  exact ⟨q, w, hchart, hperiod⟩

theorem b66m_polarization_basis_right (i : Fin 6) (a : Fin 2)
    (y : ℂ ⊗[ℤ] b60_Lattice) :
    b60_E.baseChange ℂ (b60_basis (i, a)) y =
      if a = 0 then (b60_diag i : ℂ) * b60_basis.repr y (i, 1)
      else -(b60_diag i : ℂ) * b60_basis.repr y (i, 0) := by
  conv_lhs => rw [← b60_basis.sum_repr y]
  simp only [map_sum, map_smul, smul_eq_mul, b60_pairing_basis,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a <;> simp [b60_pairing_basis] <;> ring

theorem b66m_normalized_periods_complex (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (w : b3_HolForm ℂ (rf8_fibre R.C t)) (n : ℂ ⊗[ℤ] b60_Lattice)
    (hw : ∀ x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s,
      (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) R.P s t x).val w =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n) :
    (b66m_transportPeriods R s t).flip w =
      ((b60_E.baseChange ℂ).flip n).comp (b64b_complexMarking _ m).toLinearMap := by
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v u hv hu => simp only [map_add, hv, hu]
  | tmul c x =>
    have h1 : (b66m_transportPeriods R s t).flip w (1 ⊗ₜ[ℤ] x) =
        (((b60_E.baseChange ℂ).flip n).comp
          (b64b_complexMarking _ m).toLinearMap) (1 ⊗ₜ[ℤ] x) := by
      simpa only [b66m_transportPeriods, LinearMap.comp_apply, LinearMap.codRestrict_apply,
        b3A_toDual, LinearMap.coe_mk, AddHom.coe_mk, b3_cplxPeriod,
        LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, Pi.smul_apply,
        one_smul, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply,
        AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply, LinearEquiv.coe_coe]
        using hw x
    have hc : c ⊗ₜ[ℤ] x = c • (1 ⊗ₜ[ℤ] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc, map_smul, map_smul, h1]

theorem b66m_polarization_right_injective :
    Function.Injective (b60_E.baseChange ℂ).flip := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro y hy
  apply b60_basis.repr.injective
  ext p
  obtain ⟨i, a⟩ := p
  have hd : (b60_diag i : ℂ) ≠ 0 := by
    fin_cases i <;> norm_num [b60_diag]
  have h (b : Fin 2) : b60_E.baseChange ℂ (b60_basis (i, b)) y = 0 := by
    exact congrArg (fun f : Module.Dual ℂ (ℂ ⊗[ℤ] b60_Lattice) =>
      f (b60_basis (i, b))) hy
  have h0 := h 0
  have h1 := h 1
  rw [b66m_polarization_basis_right] at h0 h1
  simp only [ite_true] at h0
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at h1
  fin_cases a
  · simpa using (mul_eq_zero.mp h1).resolve_left (neg_ne_zero.mpr hd)
  · simpa using (mul_eq_zero.mp h0).resolve_left hd

theorem b66m_normalized_frames_independent (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (w : Fin 2 × Fin 3 → b3_HolForm ℂ (rf8_fibre R.C t))
    (hw : ∀ (ij : Fin 2 × Fin 3)
      (x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s),
      (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) R.P s t x).val (w ij) =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
          (b60_frame (b64i_period R s m t.val) ij)) : LinearIndependent ℂ w := by
  let F := (LinearMap.dualMap (b64b_complexMarking _ m).toLinearMap).comp
    (b60_E.baseChange ℂ).flip
  have hF : Function.Injective F := by
    intro a b hab
    apply b66m_polarization_right_injective
    apply LinearMap.ext
    intro y
    obtain ⟨v, rfl⟩ := (b64b_complexMarking _ m).surjective y
    exact congrArg (fun f => f v) hab
  have hli := (b60_frame_independent (b64i_period R s m t.val)).map' F
    (LinearMap.ker_eq_bot_of_injective hF)
  apply LinearIndependent.of_comp (b66m_transportPeriods R s t).flip
  have heq : (b66m_transportPeriods R s t).flip ∘ w =
      F ∘ b60_frame (b64i_period R s m t.val) := by
    funext ij
    exact b66m_normalized_periods_complex R s t m (w ij) _ (hw ij)
  rw [heq]
  exact hli

theorem b66m_chart_frames_independent (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : Fin 2 × Fin 3 → b66g_primitiveForms R t)
    (w : Fin 2 × Fin 3 → b3_HolForm ℂ (rf8_fibre R.C t))
    (hc : ∀ ij, (w ij).val = b66m_chartForm R t (q ij).val)
    (hw : LinearIndependent ℂ w) : LinearIndependent ℂ q := by
  obtain ⟨M, hM⟩ := b66m_chart_comparison R t
  let I : b66g_primitiveForms R t →ₗ[ℂ] b66g_forms R t 1 :=
    Submodule.inclusion inf_le_left
  have heq : M.toLinearMap.comp I ∘ q = w := by
    funext ij
    apply Subtype.ext
    exact (hM (I (q ij))).trans (hc ij).symm
  apply LinearIndependent.of_comp (M.toLinearMap.comp I)
  rwa [heq]

theorem b66m_primitive_frame_span (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : Fin 2 × Fin 3 → b66g_primitiveForms R t) (hq : LinearIndependent ℂ q) :
    Submodule.span ℂ (Set.range q) = ⊤ := by
  apply hq.span_eq_top_of_card_eq_finrank
  rw [(b66g_primitive_comparison R t).2]
  decide

theorem b66m_normalized_basis (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    : ∃ (q : Fin 2 × Fin 3 → b66g_primitiveForms R t)
      (w : Fin 2 × Fin 3 → b3_HolForm ℂ (rf8_fibre R.C t)),
      (∀ ij, (w ij).val = b66m_chartForm R t (q ij).val) ∧
      LinearIndependent ℂ q ∧
      Submodule.span ℂ (Set.range q) = ⊤ ∧
      ∀ (ij : Fin 2 × Fin 3)
        (x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s),
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val (w ij) =
          b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
            (b60_frame (b64i_period R s m t.val) ij) := by
  obtain ⟨q, w, hc, hp⟩ := b66m_normalized_frames R s t m hJ hpol
  have hw := b66m_normalized_frames_independent R s t m w hp
  have hq := b66m_chart_frames_independent R t q w hc hw
  exact ⟨q, w, hc, hq, b66m_primitive_frame_span R t q hq, hp⟩

theorem b66m_polarized_frame_data (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y) :
    ∃ (q r : Fin 3 → b66g_primitiveForms R t)
      (ω η : Fin 3 → b3_HolForm ℂ (rf8_fibre R.C t)) (κ : ℂ),
      (κ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ∨
        κ = -(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ∧
      (∀ i, (ω i).val = b66m_chartForm R t (q i).val ∧
        (η i).val = b66m_chartForm R t (r i).val) ∧
      LinearIndependent ℂ (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q ij.2 else r ij.2) ∧
      Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 3 =>
        if ij.1 = 0 then q ij.2 else r ij.2)) = ⊤ ∧
      (∀ (i : Fin 3) (x : b63l_parameterLattice mr_base R.C R.hC
        (b6t_polydisc mr_base) (Subset.refl _) s),
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val (ω i) =
            b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
              (b60_frame (b64i_period R s m t.val) (0, i)) ∧
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val (η i) =
            b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
              (b60_frame (b64i_period R s m t.val) (1, i))) ∧
      IsUnit (b66m_leftMatrix (b64i_period R s m t.val) κ) := by
  obtain ⟨f, w, hc, hi, hs, hp⟩ := b66m_normalized_basis R s t m hJ hpol
  let q := fun i => f (0, i)
  let r := fun i => f (1, i)
  let κ : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  have heq : (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q ij.2 else r ij.2) = f := by
    funext ij
    obtain ⟨a, i⟩ := ij
    fin_cases a <;> simp [q, r]
  refine ⟨q, r, (fun i => w (0, i)), (fun i => w (1, i)), κ,
    Or.inl rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hc (0, i), hc (1, i)⟩
  · rwa [heq]
  · rwa [heq]
  · intro i x
    exact ⟨hp (0, i) x, hp (1, i) x⟩
  · apply b66m_leftMatrix_isUnit
    exact inv_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero)

theorem b66m_residuePairing_trace (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {y | y.val ∈ (R.atlas.A a).source}) :
    ∃ M : b66g_forms R t 1 ≃ₗ[ℂ] b3_HolForm ℂ (rf8_fibre R.C t),
      (∀ (Q : b66g_forms R t 1) a (p : rf8_fibre R.C t),
        p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
          (M Q).val ⟨p, w⟩ = Q.val a p.val.2 * b66m_sc_sliceD R t a p w) ∧
      ∀ (c : b66g_H1O R t) (Q : b66g_forms R t 1),
        b66m_residuePairing R t c Q = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          b66m_cechTrace R t ρ hρ c (M Q) := by
  obtain ⟨M, hM, _⟩ := (b66g_primitive_comparison R t).1
  refine ⟨M, hM, fun c Q => ?_⟩
  obtain ⟨u, hu⟩ := b66m_sc_cechProjection_surjective R t c
  have hrep : c.val = (b66g_scalarBoundaries R t).mkQ u.val := by
    rw [← hu]
    rfl
  obtain ⟨S, v, hm, hr, hv⟩ := b66m_rs_scalar_splitting R t u.val u.property
  have he := Classical.choose_spec (b66m_rs_serre_functional R t)
    u.val u.property c hrep S v hm hr hv Q
  have ht := b66m_cechTrace_residue R t ρ hρ u.val u.property S v hm hr hv
    Q (M Q) (hM Q) c hrep
  change (Classical.choose (b66m_rs_serre_functional R t)) c Q = _
  have hn : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  rw [he, ht, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem b66m_contraction_trace (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {y | y.val ∈ (R.atlas.A a).source})
    (u : b66k_Cochain R)
    (hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hm : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hr : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66k_boundary R t v a b x)
    (q r : b66g_forms R t 1) (θ : b3_HolForm ℂ (rf8_fibre R.C t))
    (hθ : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val ⟨p, w⟩ = r.val a p.val.2 * b66m_sc_sliceD R t a p w)
    (c : b66g_H1O R t)
    (hc : c.val = (b66g_scalarBoundaries R t).mkQ (b66g_contract R q.val u)) :
    b66g_residueSum R t S v (b66g_product R q.val r.val) =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * b66m_cechTrace R t ρ hρ c θ := by
  obtain ⟨hm', hr', hv'⟩ := b66m_tensor_splitting R t u S v hm hr hv q
  have ht := b66m_cechTrace_residue R t ρ hρ (b66g_contract R q.val u)
    (b66m_rs_contract_mem R t q.property hu) S
    (fun a z => q.val a ((R.atlas.A a).symm (t.val, z)).2 * v a z)
    hm' hr' hv' r θ hθ c hc
  rw [b66m_tensor_residue] at ht
  have hn : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  rw [ht, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem b66m_chartForm_coefficient (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_forms R t 1) (θ : b3_HolForm ℂ (rf8_fibre R.C t))
    (hθ : θ.val = b66m_chartForm R t q.val)
    (a : b66k_Index R) (p : rf8_fibre R.C t) (ha : p.val ∈ (R.atlas.A a).source)
    (w : ℂ) : θ.val ⟨p, w⟩ = q.val a p.val.2 * b66m_sc_sliceD R t a p w := by
  obtain ⟨M, hM, _⟩ := (b66g_primitive_comparison R t).1
  have heq : M q = θ := by
    apply Subtype.ext
    rw [hθ]
    funext y
    have hp : y.1.val = (t, y.1.val.2) := Prod.ext y.1.property rfl
    have hy : y.1.val ∈ (R.atlas.A (t, y.1.val.2)).source := by
      rw [hp]
      exact (R.atlas.hA _).1
    exact hM q _ y.1 hy y.2
  rw [← heq]
  exact hM q a p ha w

theorem b66m_multiplicationMatrix_trace (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {y | y.val ∈ (R.atlas.A a).source})
    (q r : Fin 3 → b66g_primitiveForms R t)
    (η : Fin 3 → b3_HolForm ℂ (rf8_fibre R.C t))
    (hη : ∀ i, (η i).val = b66m_chartForm R t (r i).val)
    (S : Fin 10 → Finset R.C) (v : Fin 10 → b66k_Index R → ℂ → ℂ)
    (hm : ∀ j a z, z ∈ b66k_domain R t a → MeromorphicAt (v j a) z)
    (hr : ∀ j a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z)
    (hv : ∀ j a b x, x ∉ S j → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t (Pi.single j 1) a b x = b66k_boundary R t (v j) a b x)
    (i : Fin 9) (j : Fin 10) (c : b66g_H1O R t)
    (hc : c.val = (b66g_scalarBoundaries R t).mkQ
      (b66g_contract R (q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1).val
        (b66k_cocycle R t (Pi.single j 1)))) :
    b66m_multiplicationMatrix R t q r S v i j =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * b66m_cechTrace R t ρ hρ c
        (η ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2) := by
  rw [(b66m_residue_matrix_aux R t q r S S v v hm hr hv hm hr hv).2 i j]
  exact b66m_contraction_trace R t ρ hρ _ (b66k_cocycle_mem R t (Pi.single j 1))
    (S j) (v j) (hm j) (hr j) (hv j)
    ⟨(q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1).val,
      (q _).property.1⟩
    ⟨(r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2).val,
      (r _).property.1⟩ _ (b66m_chartForm_coefficient R t _ _ (hη _)) c hc

theorem b66m_leftMatrix_mul_apply {n : Type*} [Fintype n]
    (z : Fin 9 → ℂ) (κ : ℂ) (D : Matrix (Fin 9) n ℂ) (a : Fin 9) (j : n) :
    (b66m_leftMatrix z κ * D) a j =
      -(κ * (2 / (Complex.I * (Real.sqrt 3 : ℂ)))) *
        D (finProdFinEquiv
          (((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).2,
            ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a).1)) j := by
  rw [b66m_leftMatrix_permutation, Matrix.smul_mul, Matrix.smul_apply]
  simp [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap]

/-- The full lattice vector underlying a transported primitive marked vector. -/
def b66m_primitiveFullVector (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) :
    (ℂ ⊗[ℤ] b60_Lattice) →ₗ[ℂ] (ℂ ⊗[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t)) :=
  ((b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
    (Subset.refl _) R.P s t).baseChange ℂ).comp
      (b64b_complexMarking _ m).symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- A marked primitive filtration vector lies in the full period filtration. -/
theorem b66m_primitiveFullVector_mem (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b64i_period R s m t.val)) :
    b66m_primitiveFullVector R s t m n ∈ b3_periodF ℂ (rf8_fibre R.C t) := by
  rw [(b64i_chart R s m hJ hpol t.val t.property).2, b64c_markedF] at hn
  obtain ⟨v, hv, he⟩ := hn
  have hv' : v ∈ b63e_transportedF mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) R.P s t := by
    change v ∈ rf8_transportedFamily R s t.val at hv
    rw [rf8_transportedFamily, dite_eq_left t.property] at hv
    exact hv
  have hn' : (b64b_complexMarking _ m).symm n = v := by
    rw [← he]
    exact (b64b_complexMarking _ m).symm_apply_apply v
  change (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
    (Subset.refl _) R.P s t).baseChange ℂ ((b64b_complexMarking _ m).symm n) ∈ _
  rw [hn']
  exact hv'

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Transport and the original complex marking preserve the full bilinear pairing. -/
theorem b66m_primitiveFullVector_pairing (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (x y : ℂ ⊗[ℤ] b60_Lattice) :
    (R.Q t).baseChange ℂ (b66m_primitiveFullVector R s t m x)
      (b66m_primitiveFullVector R s t m y) = b60_E.baseChange ℂ x y := by
  obtain ⟨u, rfl⟩ := (b64b_complexMarking _ m).surjective x
  obtain ⟨v, rfl⟩ := (b64b_complexMarking _ m).surjective y
  simp only [b66m_primitiveFullVector, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | tmul c a =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add v v' hv hv' => simp only [map_add, hv, hv']
    | tmul d b =>
      have he := b66m_marked_transport_intersection_W R s t m hpol a b
      rw [← b66m_intersection_lattice_W] at he
      simp only [Complex.ofReal_intCast] at he
      have hbase : (R.Q t).baseChange ℂ
          ((b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
            (Subset.refl _) R.P s t).baseChange ℂ (1 ⊗ₜ[ℤ] a))
          ((b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
            (Subset.refl _) R.P s t).baseChange ℂ (1 ⊗ₜ[ℤ] b)) =
          b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] a))
            (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] b)) := by
        simpa only [LinearMap.baseChange_tmul, one_smul,
          LinearMap.BilinForm.baseChange_tmul, one_mul, zsmul_eq_mul, mul_one] using he.symm
      rw [show c ⊗ₜ[ℤ] a = c • (1 ⊗ₜ[ℤ] a) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        show d ⊗ₜ[ℤ] b = d • (1 ⊗ₜ[ℤ] b) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hbase]

/-- Harmonic forms of primitive filtration vectors have the original normalized primitive periods. -/
theorem b66m_primitiveFullVector_period (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (b3_periodLattice ℂ (rf8_fibre R.C t)))
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b64i_period R s m t.val))
    (x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s) :
    (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) R.P s t x).val
      (b66m_polarizedHarmonicForm R t b (b66m_primitiveFullVector R s t m n)) =
      b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n := by
  rw [b66m_polarizedHarmonicForm_period R t b _
    (b66m_primitiveFullVector_mem R s t m hJ hpol n hn)]
  have he := b66m_primitiveFullVector_pairing R s t m hpol
    (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n
  simpa only [b66m_primitiveFullVector, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.baseChange_tmul, one_smul] using he

/-- The marked primitive vector regarded as original complexified integral homology. -/
def b66m_primitiveHomology (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) :
    (ℂ ⊗[ℤ] b60_Lattice) →ₗ[ℂ] (ℂ ⊗[ℤ] b66g_Homology R s) :=
  letI : Module ℤ (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
    (Subset.refl _) s) := AddCommGroup.toIntModule _
  let i : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s →ₗ[ℤ] b66g_Homology R s :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun r x =>
        (int_smul_eq_zsmul (b6m_H1 (rf8_fibre R.C s)).isModule r x.val).symm }
  (i.baseChange ℂ).comp (b64b_complexMarking _ m).symm.toLinearMap

/-- The original homology inclusion and full transport give the same full lattice vector. -/
theorem b66m_primitiveHomology_transport (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (n : ℂ ⊗[ℤ] b60_Lattice) :
    (b66m_fullTransport R s t).baseChange ℂ (b66m_primitiveHomology R s m n) =
      b66m_primitiveFullVector R s t m n := by
  obtain ⟨v, rfl⟩ := (b64b_complexMarking _ m).surjective n
  simp only [b66m_primitiveHomology, b66m_primitiveFullVector, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x => rfl

set_option backward.isDefEq.respectTransparency false in
/-- The full harmonic trace on a primitive vector equals its original flat period derivative. -/
theorem b66m_contraction_cech_primitive_functional (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (b3_periodLattice ℂ (rf8_fibre R.C t)))
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R) (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66g_forms R t 1)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b64i_period R s m t.val)) :
    b66m_cechTrace R t ρ hρ (b66m_sc_cechProjection R t
      ⟨b66g_contract R q (b66k_cocycle R t h),
        b66m_rs_contract_mem R t hqf (b66k_cocycle_mem R t h)⟩)
      (b66m_polarizedHarmonicForm R t b (b66m_primitiveFullVector R s t m n)) =
      fderiv ℂ (b66m_flatPeriod R s θ (b66m_primitiveHomology R s m n)) t.val h := by
  rw [b66m_contraction_cech_functional R t b θ q h ρ hU ht hqf hq hρ _
    (b66m_primitiveFullVector_mem R s t m hJ hpol n hn),
    ← b66m_primitiveHomology_transport R s t m n]
  exact b66m_complexPeriodFunctional_flat R s θ t q h ρ hU ht hqf hq hρ _

/-- The original flat functional vanishes on the moving marked primitive filtration. -/
theorem b66m_primitive_flatPeriod_zero (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b64i_period R s m t.val)) :
    b66m_flatPeriod R s θ (b66m_primitiveHomology R s m n) t.val = 0 := by
  rw [b66m_flatPeriod_transport, b66m_primitiveHomology_transport]
  have he := b66m_primitiveFullVector_mem R s t m hJ hpol n hn
  change b3_cplxPeriod ℂ (rf8_fibre R.C t)
    (b66m_primitiveFullVector R s t m n) = 0 at he
  exact congrFun he _

/-- The primitive projector remains self-adjoint against a complex full lattice vector. -/
theorem b66m_projector_pairing_complex (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (l : b3_periodLattice ℂ (rf8_fibre R.C t))
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (rf8_fibre R.C t)) :
    (R.Q t).baseChange ℂ (1 ⊗ₜ[ℤ] b4_groupEnd ℂ b4b_projectorCoeff l) y =
      (R.Q t).baseChange ℂ (1 ⊗ₜ[ℤ] l)
        (b2_cplxMap (b4_groupEnd ℂ b4b_projectorCoeff) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul c k =>
    have he := (b63l_image_riemann (rf8_fibre R.C t) (R.hG t) (R.Q t) (R.hQ t)).1 l k
    simp only [b2_cplxMap, LinearMap.baseChange_tmul,
      LinearMap.BilinForm.baseChange_tmul, one_mul, zsmul_eq_mul,
      AddMonoidHom.coe_toIntLinearMap, he]

/-- The original full lattice inclusion is in the primitive projector eigenspace. -/
theorem b66m_primitiveFullVector_eigen (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (n : ℂ ⊗[ℤ] b60_Lattice) :
    b2_cplxMap (b4_groupEnd ℂ b4b_projectorCoeff) (b66m_primitiveFullVector R s t m n) =
      b4b_projectorDenominator • b66m_primitiveFullVector R s t m n := by
  obtain ⟨v, rfl⟩ := (b64b_complexMarking _ m).surjective n
  simp only [b66m_primitiveFullVector, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul c x =>
    simp only [LinearMap.baseChange_tmul, b2_cplxMap, AddMonoidHom.coe_toIntLinearMap]
    rw [b66m_transport_period_eigen]
    exact (map_zsmul (TensorProduct.mk ℤ ℂ
      (b3_periodLattice ℂ (rf8_fibre R.C t)) c) b4b_projectorDenominator _)

/-- The harmonic form of a primitive filtration vector is a primitive projector eigenform. -/
theorem b66m_primitiveFullVector_holProjector (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (b3_periodLattice ℂ (rf8_fibre R.C t)))
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b64i_period R s m t.val)) :
    b66m_holProjector R t
      (b66m_polarizedHarmonicForm R t b (b66m_primitiveFullVector R s t m n)) =
      (b4b_projectorDenominator : ℂ) •
        b66m_polarizedHarmonicForm R t b (b66m_primitiveFullVector R s t m n) := by
  let y := b66m_primitiveFullVector R s t m n
  let w := b66m_polarizedHarmonicForm R t b y
  have hy := b66m_primitiveFullVector_mem R s t m hJ hpol n hn
  have hv (l : b3_periodLattice ℂ (rf8_fibre R.C t)) :
      l.val (b66m_holProjector R t w) = (b4b_projectorDenominator : ℂ) * l.val w := by
    rw [b66m_holProjector_period R t l w]
    rw [b66m_polarizedHarmonicForm_period R t b y hy,
      b66m_projector_pairing_complex R t l y,
      b66m_primitiveFullVector_eigen R s t m n]
    rw [map_zsmul]
    rw [b66m_polarizedHarmonicForm_period R t b y hy]
    exact Int.cast_smul_eq_zsmul ℂ _ _ |>.symm
  apply sub_eq_zero.mp
  apply b3Rest2_eq_zero_of_re_lattice (Module.finrank_self ℂ)
  intro l
  let L := b3A_toDual ⟨l.val, b3A_lattice_mem_linearDual l⟩
  change (L (b66m_holProjector R t w - (b4b_projectorDenominator : ℂ) • w)).re = 0
  rw [map_sub, map_smul]
  change (l.val (b66m_holProjector R t w) - (b4b_projectorDenominator : ℂ) * l.val w).re = 0
  rw [hv, sub_self]
  rfl

/-- A primitive projector eigenform has an actual primitive coefficient representative. -/
theorem b66m_primitive_coefficient_of_holProjector (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (w : b3_HolForm ℂ (rf8_fibre R.C t))
    (hw : b66m_holProjector R t w = (b4b_projectorDenominator : ℂ) • w) :
    ∃ q : b66g_primitiveForms R t, w.val = b66m_chartForm R t q.val := by
  obtain ⟨M, hM, hP⟩ := b66m_chart_projector R t
  obtain ⟨qP, hqP, hwP⟩ := hP (M.symm w)
  have hp : qP.val ∈ b66g_primitiveForms R t :=
    ⟨qP.property, M.symm w, hqP.symm⟩
  let z : ℂ := (b4b_projectorDenominator : ℂ)⁻¹
  let qF : b66g_forms R t 1 := z • qP
  have hqF : qF.val ∈ b66g_primitiveForms R t :=
    (b66g_primitiveForms R t).smul_mem z hp
  have he : M qF = w := by
    change M (z • qP) = w
    rw [map_smul, hwP, M.apply_symm_apply, hw, smul_smul]
    have hd : (b4b_projectorDenominator : ℂ) ≠ 0 := by
      norm_num [b4b_projectorDenominator]
    rw [show z * (b4b_projectorDenominator : ℂ) = 1 from inv_mul_cancel₀ hd, one_smul]
  refine ⟨⟨qF.val, hqF⟩, ?_⟩
  rw [← he]
  exact hM qF

/-- A relative form with the literal coefficient law evaluates to the supplied chart form. -/
theorem b66m_relative_extension_chartForm (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R) (w : b3_HolForm ℂ (rf8_fibre R.C t))
    (hw : w.val = b66m_chartForm R t q)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ v : ℂ,
      θ.val t ⟨p, v⟩ = q a p.val.2 * b66m_sc_sliceD R t a p v) :
    b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) θ t = w := by
  apply Subtype.ext
  rw [hw]
  funext p
  have hp : p.1.val = (t, p.1.val.2) := Prod.ext p.1.property rfl
  have ha : p.1.val ∈ (R.atlas.A (t, p.1.val.2)).source := by
    rw [hp]
    exact (R.atlas.hA _).1
  exact hq (t, p.1.val.2) p.1 ha p.2

set_option backward.isDefEq.respectTransparency false in
/-- Normalized integral periods determine the flat functional on every marked complex vector. -/
theorem b66m_normalized_flatPeriod (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (w : b3_HolForm ℂ (rf8_fibre R.C t)) (n : ℂ ⊗[ℤ] b60_Lattice)
    (hθ : b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) θ t = w)
    (hw : ∀ x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s,
      (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) R.P s t x).val w =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n)
    (x : ℂ ⊗[ℤ] b60_Lattice) :
    b66m_flatPeriod R s θ (b66m_primitiveHomology R s m x) t.val =
      b60_E.baseChange ℂ x n := by
  rw [b66m_flatPeriod_transport, b66m_primitiveHomology_transport, hθ]
  have he := LinearMap.congr_fun (b66m_normalized_periods_complex R s t m w n hw)
    ((b64b_complexMarking _ m).symm x)
  simpa only [b66m_transportPeriods, b66m_primitiveFullVector, LinearMap.flip_apply,
    LinearMap.comp_apply, LinearMap.codRestrict_apply, b3A_toDual,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.BilinForm.flip_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using he

/-- Positive head vectors pair with the negative graph frame in the original normalization. -/
theorem b66m_head_pairing (z : Fin 9 → ℂ) (k i : Fin 3) :
    b60_E.baseChange ℂ (b60_eigen 1 (Fin.castAdd 3 k)) (b60_frame z (0, i)) =
      if k = i then -(2 / (Complex.I * (Real.sqrt 3 : ℂ))) else 0 := by
  fin_cases k <;> fin_cases i <;>
    simp [b60_frame, b60_pairing_eigen, Fin.sum_univ_succ, b60_diag] <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- The original normalized flat functional calculates the polarized positive graph derivative. -/
theorem b66m_normalized_graph_derivative (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (hU : IsOpen U) (ht : t.val ∈ U)
    (w : b3_HolForm ℂ (rf8_fibre R.C t)) (i j : Fin 3) (h : Fin 10 → ℂ)
    (hθ : b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) θ t = w)
    (hw : ∀ x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s,
      (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) R.P s t x).val w =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
          (b60_frame (b64i_period R s m t.val) (0, i))) :
    fderiv ℂ (b66m_flatPeriod R s θ (b66m_primitiveHomology R s m
      (b60_frame (b64i_period R s m t.val) (1, j)))) t.val h =
      (2 / (Complex.I * (Real.sqrt 3 : ℂ))) *
        (fderiv ℂ (b64i_period R s m) t.val h) (finProdFinEquiv (j, i)) := by
  let P := (b66m_flatPeriod R s θ).comp (b66m_primitiveHomology R s m)
  have hP (n : ℂ ⊗[ℤ] b60_Lattice) : DifferentiableAt ℂ (P n) t.val :=
    (b66m_flatPeriod_analytic R s θ hU _ t.val ⟨t.property, ht⟩).differentiableAt
  have hz := (b64i_analytic R s m hJ hpol t.val t.property).differentiableAt
  have hzero : ∀ᶠ u in 𝓝 t.val, P (b60_frame (b64i_period R s m u) (1, j)) u = 0 := by
    filter_upwards [(rf5_polydisc_isOpen mr_base).mem_nhds t.property] with u hu
    exact b66m_primitive_flatPeriod_zero R s ⟨u, hu⟩ m hJ hpol θ _
      (Submodule.subset_span ⟨(1, j), rfl⟩)
  change fderiv ℂ (P (b60_frame (b64i_period R s m t.val) (1, j))) t.val h = _
  rw [b66m_positive_frame_derivative P (b64i_period R s m) t.val h j hP hz hzero]
  have hp (k : Fin 3) : P (b60_eigen 1 (Fin.castAdd 3 k)) t.val =
      if k = i then -(2 / (Complex.I * (Real.sqrt 3 : ℂ))) else 0 := by
    rw [show P (b60_eigen 1 (Fin.castAdd 3 k)) t.val =
        b60_E.baseChange ℂ (b60_eigen 1 (Fin.castAdd 3 k))
          (b60_frame (b64i_period R s m t.val) (0, i)) from
      b66m_normalized_flatPeriod R s t m θ w _ hθ hw _, b66m_head_pairing]
  simp_rw [hp]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Contraction against a normalized positive harmonic frame gives the ordered graph derivative. -/
theorem b66m_normalized_contraction_trace (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (b3_periodLattice ℂ (rf8_fibre R.C t)))
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (q : b66g_primitiveForms R t) (w : b3_HolForm ℂ (rf8_fibre R.C t))
    (i k : Fin 3) (h : Fin 10 → ℂ)
    (hw : w.val = b66m_chartForm R t q.val)
    (hp : ∀ x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s,
      (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) R.P s t x).val w =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
          (b60_frame (b64i_period R s m t.val) (0, i))) :
    b66m_cechTrace R t ρ hρ (b66m_sc_cechProjection R t
      ⟨b66g_contract R q.val (b66k_cocycle R t h),
        b66m_rs_contract_mem R t q.property.1 (b66k_cocycle_mem R t h)⟩)
      (b66m_polarizedHarmonicForm R t b (b66m_primitiveFullVector R s t m
        (b60_frame (b64i_period R s m t.val) (1, k)))) =
      (2 / (Complex.I * (Real.sqrt 3 : ℂ))) *
        (fderiv ℂ (b64i_period R s m) t.val h) (finProdFinEquiv (k, i)) := by
  obtain ⟨U, hU, ht, _, θ, hq⟩ :=
    b66m_coefficient_relative_extension R t ⟨q.val, q.property.1⟩
  rw [b66m_contraction_cech_primitive_functional R s t m hJ hpol b θ q.val h ρ
    hU ht q.property.1 hq hρ _ (Submodule.subset_span ⟨(1, k), rfl⟩)]
  exact b66m_normalized_graph_derivative R s t m hJ hpol θ hU ht w i k h
    (b66m_relative_extension_chartForm R t θ q.val w hw hq) hp

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b66m_polarized_matrix_aux (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y) :
    ∃ (q r : Fin 3 → b66g_primitiveForms R t)
      (ω η : Fin 3 → b3_HolForm ℂ (rf8_fibre R.C t)) (κ : ℂ),
      (κ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ∨
        κ = -(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ∧
      (∀ i, (ω i).val = b66m_chartForm R t (q i).val ∧
        (η i).val = b66m_chartForm R t (r i).val) ∧
      LinearIndependent ℂ (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q ij.2 else r ij.2) ∧
      Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 3 =>
        if ij.1 = 0 then q ij.2 else r ij.2)) = ⊤ ∧
      (∀ (i : Fin 3) (x : b63l_parameterLattice mr_base R.C R.hC
        (b6t_polydisc mr_base) (Subset.refl _) s),
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val (ω i) =
            b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
              (b60_frame (b64i_period R s m t.val) (0, i)) ∧
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val (η i) =
            b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
              (b60_frame (b64i_period R s m t.val) (1, i))) ∧
      IsUnit (b66m_leftMatrix (b64i_period R s m t.val) κ) ∧
      ∀ (S : Fin 10 → Finset R.C) (v : Fin 10 → b66k_Index R → ℂ → ℂ)
      (_hmero : ∀ j a z, z ∈ b66k_domain R t a → MeromorphicAt (v j a) z)
      (_hreg : ∀ j a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z)
      (_hv : ∀ j a b x, x ∉ S j → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        b66k_cocycle R t (Pi.single j 1) a b x = b66k_boundary R t (v j) a b x),
        b66m_multiplicationMatrix R t q r S v =
          b66m_leftMatrix (b64i_period R s m t.val) κ *
            LinearMap.toMatrix' (fderiv ℂ (b64i_period R s m) t.val).toLinearMap *
              (1 : Matrix (Fin 10) (Fin 10) ℂ) := by
  letI := b3_periodLattice_finite (E := ℂ) (C := rf8_fibre R.C t) (Module.finrank_self ℂ)
  letI := b3_periodLattice_free (E := ℂ) (C := rf8_fibre R.C t)
  let b := Module.Free.chooseBasis ℤ (b3_periodLattice ℂ (rf8_fibre R.C t))
  let w := fun ij : Fin 2 × Fin 3 => b66m_polarizedHarmonicForm R t b
    (b66m_primitiveFullVector R s t m (b60_frame (b64i_period R s m t.val) ij))
  have hf (ij : Fin 2 × Fin 3) :
      ∃ q : b66g_primitiveForms R t, (w ij).val = b66m_chartForm R t q.val := by
    apply b66m_primitive_coefficient_of_holProjector R t (w ij)
    exact b66m_primitiveFullVector_holProjector R s t m hJ hpol b _
      (Submodule.subset_span ⟨ij, rfl⟩)
  choose f hc using hf
  have hp (ij : Fin 2 × Fin 3)
      (x : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s) :
      (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) R.P s t x).val (w ij) =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
          (b60_frame (b64i_period R s m t.val) ij) :=
    b66m_primitiveFullVector_period R s t m hJ hpol b _
      (Submodule.subset_span ⟨ij, rfl⟩) x
  have hi := b66m_chart_frames_independent R t f w hc
    (b66m_normalized_frames_independent R s t m w hp)
  have hs := b66m_primitive_frame_span R t f hi
  let q := fun i => f (0, i)
  let r := fun i => f (1, i)
  let κ : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)⁻¹
  have heq : (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q ij.2 else r ij.2) = f := by
    funext ij
    obtain ⟨a, i⟩ := ij
    fin_cases a <;> simp [q, r]
  refine ⟨q, r, (fun i => w (0, i)), (fun i => w (1, i)), κ,
    Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hc (0, i), hc (1, i)⟩
  · rwa [heq]
  · rwa [heq]
  · intro i x
    exact ⟨hp (0, i) x, hp (1, i) x⟩
  · apply b66m_leftMatrix_isUnit
    exact neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero))
  · intro S v hm hr hv
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℂ))
      (M := rf8_fibre R.C t) isClosed_univ
      (fun c => {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A c).source})
      (fun c => b66m_sc_open_source R t c)
      (fun y _ => mem_iUnion.mpr ⟨y.val, (R.atlas.hA y.val).1⟩)
    rw [Matrix.mul_one]
    ext a j
    let ij := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a
    let c := b66m_sc_cechProjection R t
      ⟨b66g_contract R (q ij.1).val (b66k_cocycle R t (Pi.single j 1)),
        b66m_rs_contract_mem R t (q ij.1).property.1
          (b66k_cocycle_mem R t (Pi.single j 1))⟩
    rw [b66m_multiplicationMatrix_trace R t ρ hρ q r (fun i => w (1, i))
      (fun i => hc (1, i)) S v hm hr hv a j c rfl]
    change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * b66m_cechTrace R t ρ hρ c (w (1, ij.2)) = _
    rw [b66m_normalized_contraction_trace R s t m hJ hpol b ρ hρ
      (q ij.1) (w (0, ij.1)) ij.1 ij.2 (Pi.single j 1) (hc (0, ij.1)) (hp (0, ij.1)),
      b66m_leftMatrix_mul_apply, LinearMap.toMatrix'_apply]
    dsimp only [κ, ij]
    simp only [ContinuousLinearMap.coe_coe]
    ring


theorem b66m_jet_codiff_aux (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (curve : ℂ → Fin 10 → ℂ) (hcurve : ContinuousAt curve 0)
    (hzero : curve 0 ∈ b6t_polydisc mr_base) :
    ∃ (q r : (t : b6t_polydisc mr_base) → Fin 3 → b66g_primitiveForms R t)
      (S : (t : b6t_polydisc mr_base) → Fin 10 → Finset R.C)
      (v : (t : b6t_polydisc mr_base) → Fin 10 → b66k_Index R → ℂ → ℂ),
      (∀ t, LinearIndependent ℂ
        (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q t ij.2 else r t ij.2)) ∧
      (∀ t j a z, z ∈ b66k_domain R t a → MeromorphicAt (v t j a) z) ∧
      (∀ t j a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S t j → AnalyticAt ℂ (v t j a) z) ∧
      (∀ t j a b x, x ∉ S t j → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        b66k_cocycle R t (Pi.single j 1) a b x = b66k_boundary R t (v t j) a b x) ∧
      ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
        ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
          (∃ κ : ℂ, (κ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ∨
            κ = -(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ∧
            L = b66m_leftMatrix (b64i_period R s m (curve θ)) κ) ∧
          T = 1 ∧
          b66m_jet R q r S v curve θ = L * LinearMap.toMatrix'
            (fderiv ℂ (b64i_period R s m) (curve θ) :
              (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T := by
  have hf := fun t : b6t_polydisc mr_base =>
    b66m_polarized_matrix_aux R s t m hJ hpol
  choose q r ω η κ hk hforms hlin hspan hperiod hunit hmatrix using hf
  have hs := fun (t : b6t_polydisc mr_base) (j : Fin 10) =>
    b66g_meromorphic_splitting R t (b66k_cocycle R t (Pi.single j 1))
      (b66k_cocycle_mem R t (Pi.single j 1))
  choose S v hm hr hv using hs
  refine ⟨q, r, S, v, hlin, hm, hr, hv, ?_⟩
  have hnear : ∀ᶠ θ in 𝓝 (0 : ℂ), curve θ ∈ b6t_polydisc mr_base :=
    hcurve.eventually ((b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).2.2.1.mem_nhds hzero)
  filter_upwards [hnear] with θ hθ
  let t : b6t_polydisc mr_base := ⟨curve θ, hθ⟩
  refine ⟨b66m_leftMatrix (b64i_period R s m (curve θ)) (κ t),
    1, hunit t, isUnit_one, ⟨κ t, hk t, rfl⟩, rfl, ?_⟩
  rw [b66m_jet, dite_eq_left hθ]
  exact hmatrix t (S t) (v t) (hm t) (hr t) (hv t)

end HodgeLean.Foundations.Program

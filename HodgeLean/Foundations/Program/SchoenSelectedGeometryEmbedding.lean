import HodgeLean.Foundations.Program.RiemannRoch
import HodgeLean.Foundations.Program.HurwitzPrym

noncomputable section
set_option maxHeartbeats 400000
open Manifold
open Filter Set
open scoped ContDiff Topology
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The section dimension for a divisor of degree greater than the canonical degree.
Source: Forster, Lectures on Riemann Surfaces, GTM 81, §16. -/
theorem s0_high_degree_section_dimension
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (D : C →₀ ℤ)
    (hD : 2 * (Module.finrank ℂ (b3_HolForm ℂ C) : ℤ) - 2 < b4c_deg D) :
    (Module.finrank ℂ (b4c_L (E := ℂ) D) : ℤ) =
      b4c_deg D - Module.finrank ℂ (b3_HolForm ℂ C) + 1 := by
  obtain ⟨w, hw, hgw⟩ := b4c_exists_meroForm (C := C) (Module.finrank_self ℂ)
  have hneg : b4c_deg (b4c_divForm (hE := Module.finrank_self ℂ) w - D) < 0 := by
    rw [RiemannRochAna_deg_sub, b4c_deg_canonical (Module.finrank_self ℂ) w hw hgw]
    omega
  have hz := RiemannRochAna_L_eq_bot_of_deg_neg (Module.finrank_self ℂ) _ hneg
  have hr := b4c_riemannRoch (Module.finrank_self ℂ) D w hw hgw
  rw [hz, finrank_bot, Nat.cast_zero, sub_zero] at hr
  exact hr

#print axioms s0_high_degree_section_dimension

theorem s0_single_pole_function
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (p : C) (n : ℕ) (hn : 2 * Module.finrank ℂ (b3_HolForm ℂ C) ≤ n) :
    ∃ F : b4c_MeroFun ℂ C, (∃ x, F x ≠ (0 : ℂ)) ∧
      b4c_ord ℂ F p = -(n : ℤ) ∧
      ∀ x, x ≠ p → 0 ≤ b4c_ord ℂ F x := by
  classical
  let D : C →₀ ℤ := Finsupp.single p ((n : ℤ) - 1)
  have hd : b4c_deg D = (n : ℤ) - 1 := by
    simp only [D, b4c_deg, Finsupp.sum_single_index, add_zero]
  have hb : b4c_deg (D + Finsupp.single p 1) = (n : ℤ) := by
    rw [RiemannRochAna_deg_add, hd]
    simp [b4c_deg]
  have hdn : 2 * (Module.finrank ℂ (b3_HolForm ℂ C) : ℤ) - 2 < b4c_deg D := by
    rw [hd]
    have hn' : 2 * (Module.finrank ℂ (b3_HolForm ℂ C) : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hn
    omega
  have hbn : 2 * (Module.finrank ℂ (b3_HolForm ℂ C) : ℤ) - 2 <
      b4c_deg (D + Finsupp.single p 1) := by
    have hn' : 2 * (Module.finrank ℂ (b3_HolForm ℂ C) : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hn
    rw [hb]
    omega
  have hdim := s0_high_degree_section_dimension D hdn
  have hdim' := s0_high_degree_section_dimension (D + Finsupp.single p 1) hbn
  have hlt : Module.finrank ℂ (b4c_L (E := ℂ) D) <
      Module.finrank ℂ (b4c_L (E := ℂ) (D + Finsupp.single p 1)) := by omega
  obtain ⟨F, hF, hbound, hord⟩ :=
    RiemannRochRR_exists_exact_order (Module.finrank_self ℂ) D p hlt
  refine ⟨F, hF, ?_, ?_⟩
  · simp only [D, Finsupp.single_eq_same] at hord
    omega
  · intro x hx
    simpa only [D, Finsupp.add_apply, Finsupp.single_eq_of_ne hx, add_zero] using hbound x

#print axioms s0_single_pole_function

theorem s0_meromorphic_separates_points
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (x y : C) (hxy : x ≠ y) :
    ∃ F : b4c_MeroFun ℂ C, F x = OnePoint.infty ∧ F y ≠ OnePoint.infty := by
  let n := 2 * Module.finrank ℂ (b3_HolForm ℂ C) + 1
  obtain ⟨F, _, hp, hb⟩ := s0_single_pole_function x n (by omega)
  have hn : 0 < n := by omega
  have hpx : F x = OnePoint.infty := by
    by_contra h
    unfold b4c_ord at hp
    rw [ite_eq_right h] at hp
    split_ifs at hp <;> omega
  exact ⟨F, hpx, RiemannRochAna_ne_infty_of_ord_nonneg
    (Module.finrank_self ℂ) F y (hb y hxy.symm)⟩

#print axioms s0_meromorphic_separates_points

theorem s0_meromorphic_locally_injective
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (p : C) : ∃ (F : b4c_MeroFun ℂ C) (U : Set C),
      IsOpen U ∧ p ∈ U ∧ Set.InjOn F U := by
  obtain ⟨F, _, hFp, ha, hd⟩ :=
    RiemannRochEichler_unramified_function (Module.finrank_self ℂ) p
  let f := RiemannRochEichler_functionLocal (Module.finrank_self ℂ) F p
  have hs : HasStrictDerivAt f (deriv f 0) 0 := ha.hasStrictDerivAt
  let inv := hs.localInverse f (deriv f 0) 0 hd
  have hinv : ∀ᶠ z in 𝓝 (0 : ℂ), inv (f z) = z := hs.eventually_left_inverse hd
  obtain ⟨V, hV, hVo, hV0⟩ := mem_nhds_iff.mp hinv
  let φ := extChartAt 𝓘(ℂ, ℂ) p
  let q := RiemannRochAna_coordinate (Module.finrank_self ℂ) p
  have hq : ContinuousAt q p :=
    (RiemannRochAna_coordinate_analytic (Module.finrank_self ℂ) p p
      (mem_extChartAt_source p)).continuousAt
  have hq0 : q p = 0 := RiemannRochAna_coordinate_self (Module.finrank_self ℂ) p
  have hU : φ.source ∩ q ⁻¹' V ∈ 𝓝 p := inter_mem
    ((isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p))
    (hq.preimage_mem_nhds (hq0 ▸ hVo.mem_nhds hV0))
  obtain ⟨U, hsub, ho, hp⟩ := mem_nhds_iff.mp hU
  refine ⟨F, U, ho, hp, ?_⟩
  intro x hx y hy hxy
  have hval (z : C) (hz : z ∈ φ.source) : f (q z) = (F z).elim 0 id := by
    dsimp only [f, q, RiemannRochEichler_functionLocal, RiemannRochAna_coordinate]
    rw [ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel,
      (extChartAt 𝓘(ℂ, ℂ) p).left_inv hz]
  have he : f (q x) = f (q y) := by rw [hval x (hsub hx).1, hval y (hsub hy).1, hxy]
  have hqq : q x = q y := by
    have hh := congrArg inv he
    rw [hV (hsub hx).2, hV (hsub hy).2] at hh
    exact hh
  apply φ.injOn (hsub hx).1 (hsub hy).1
  have hh := congrArg (b4cov_lineEquiv (Module.finrank_self ℂ)) hqq
  simp only [q, RiemannRochAna_coordinate, ContinuousLinearEquiv.apply_symm_apply] at hh
  simpa only [φ, sub_add_cancel] using congrArg (fun z : ℂ ↦ z + φ p) hh

#print axioms s0_meromorphic_locally_injective

theorem s0_meromorphic_unramified_neighborhood
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (p : C) : ∃ (F : b4c_MeroFun ℂ C) (U : Set C),
      IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F x ≠ 0 := by
  obtain ⟨F, hnc, hFp, ha, hd⟩ :=
    RiemannRochEichler_unramified_function (Module.finrank_self ℂ) p
  have hzero : RiemannRochEichler_functionLocal (Module.finrank_self ℂ) F p 0 = 0 := by
    simp [RiemannRochEichler_functionLocal, hFp]
  have ho : meromorphicOrderAt
      (RiemannRochEichler_functionLocal (Module.finrank_self ℂ) F p) 0 = 1 := by
    rw [ha.meromorphicOrderAt_eq,
      ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hd]
    rfl
  have hnz : ∃ x, F x ≠ (0 : ℂ) := by
    obtain ⟨a, b, hab⟩ := hnc
    by_cases ha : F a = (0 : ℂ)
    · exact ⟨b, fun hb ↦ hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  have he := RiemannRochEichler_ord_eq_local (Module.finrank_self ℂ) F hnz p
  rw [ho] at he
  have hord : b4c_ord ℂ F p = 1 := by exact_mod_cast he
  have hram : b4_ramIndex ℂ ℂ F p = 1 := by
    simp [b4c_ord, hFp] at hord
    exact_mod_cast hord
  have hfin := b4_ramification_finite (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) F F.property.1 hnc
  refine ⟨F, {x | 2 ≤ b4_ramIndex ℂ ℂ F x}ᶜ, hfin.isClosed.isOpen_compl, ?_, ?_⟩
  · simpa only [mem_compl_iff, mem_setOf_eq, hram] using (by omega : ¬ 2 ≤ (1 : ℕ))
  · intro x hx
    have hpos := b4_ramIndex_pos (Module.finrank_self ℂ) (Module.finrank_self ℂ)
      F F.property.1 hnc x
    have hlt : ¬ 2 ≤ b4_ramIndex ℂ ℂ F x := hx
    apply (b4_ramIndex_eq_one_iff F F.property.1 x).mp
    omega

#print axioms s0_meromorphic_unramified_neighborhood

end HodgeLean.Foundations.Program

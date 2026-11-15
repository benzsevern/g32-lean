import HodgeLean.Foundations.Program.SchoenCycleResidueSlice
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.DivisorDegreeFacts

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology
open TauCeti.Contour
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Forster, Lectures on Riemann Surfaces, §14, linearity of meromorphic differentials. -/
theorem meromorphicForm_finite_linear_combination
    (h : Module.finrank ℂ E = 1) {ι : Type*} [Fintype ι]
    (w : ι → b4c_MeroForm E C h) (a : ι → ℂ) :
    b4c_IsMeroForm h (∑ i, a i • (w i : TangentBundle 𝓘(ℂ, E) C → ℂ)) := by
  classical
  constructor
  · intro p b u v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      fun i => (w i).property.1 p b u v, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc, mul_left_comm]
  · intro p
    have he : HurwitzPrymRR_loc h
        (∑ i, a i • (w i : TangentBundle 𝓘(ℂ, E) C → ℂ)) p =
        ∑ i, a i • HurwitzPrymRR_loc h (w i) p := by
      funext z
      simp only [HurwitzPrymRR_loc, b4cov_coef, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    rw [he]
    exact MeromorphicAt.sum (s := Finset.univ) (fun i _ =>
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a i) 0).meromorphicAt.smul
        ((w i).property.2 p))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Forster, Lectures on Riemann Surfaces, §18, third-kind differentials with prescribed residues. -/
theorem thirdKindDifferential_of_degree_zero
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (p : C) (D : C →₀ ℤ)
    (hdeg : b4c_deg D = 0) :
    ∃ w : b4c_MeroForm E C h,
      (∀ x, b4c_res (hE := h) w x = (D x : ℂ)) ∧
      (∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0) ∧
      ∃ q : C, q ∉ D.support ∧
        ∀ x, x ∉ D.support → x ≠ q → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0 := by
  classical
  obtain ⟨q, hq⟩ := RiemannRochAna_exists_unmarked h p (fun x : D.support => x.val)
  have hqs : q ∉ D.support := fun hx => hq ⟨⟨q, hx⟩, rfl⟩
  have hne (i : D.support) : q ≠ i.val := fun he => hqs (he ▸ i.property)
  choose v hv using fun i : D.support => s2e_regular_two_point_differential h q i.val (hne i)
  let a : D.support → ℂ := fun i => (D i : ℂ)
  let w : b4c_MeroForm E C h := ⟨∑ i, a i • (v i : TangentBundle 𝓘(ℂ, E) C → ℂ),
    meromorphicForm_finite_linear_combination h v a⟩
  have hloc (x : C) : HurwitzPrymRR_loc h w x = ∑ i, a i • HurwitzPrymRR_loc h (v i) x := by
    funext z
    simp only [w, HurwitzPrymRR_loc, b4cov_coef, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  have hsum : ∑ i : D.support, a i = 0 := by
    change ∑ i : D.support, (D i : ℂ) = 0
    have hz : ∑ i : D.support, D i = 0 := (Finset.sum_attach D.support D).trans hdeg
    exact_mod_cast hz
  refine ⟨w, ?_, ?_, q, hqs, ?_⟩
  · intro x
    change b4c_res (hE := h) (∑ i, a i • (v i : TangentBundle 𝓘(ℂ, E) C → ℂ)) x = _
    rw [s2e_residue_linear_combination]
    by_cases hxq : x = q
    · subst x
      simp only [fun i => (hv i).1, mul_neg, mul_one, Finset.sum_neg_distrib, hsum,
        neg_zero, Finsupp.notMem_support_iff.mp hqs, Int.cast_zero]
    · have hres (i : D.support) : b4c_res (hE := h) (v i) x = if i.val = x then 1 else 0 := by
        split_ifs with he
        · rw [← he]; exact (hv i).2.1
        · exact residue_eq_zero_of_analyticAt ((hv i).2.2.2 x hxq (Ne.symm he))
      simp only [hres, mul_ite, mul_one, mul_zero]
      by_cases hx : x ∈ D.support
      · rw [Finset.sum_eq_single (⟨x, hx⟩ : D.support)]
        · simp [a]
        · intro i _ hi
          exact ite_eq_right (fun he => hi (Subtype.ext he))
        · simp
      · have hn (i : D.support) : i.val ≠ x := fun he => hx (he ▸ i.property)
        simp only [hn, ite_false, Finset.sum_const_zero, Finsupp.notMem_support_iff.mp hx,
          Int.cast_zero]
  · intro x
    rw [hloc]
    apply s2e_meromorphic_order_sum_lower_bound Finset.univ _ 0 (-1)
    · intro i _
      exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a i) 0).meromorphicAt.smul
        ((v i).property.2 x)
    · intro i _
      by_cases ha : a i = 0
      · rw [ha, zero_smul]
        change (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun _ : ℂ => (0 : ℂ)) 0
        rw [meromorphicOrderAt_const, ite_eq_left rfl]
        exact le_top
      · rw [meromorphicOrderAt_const_smul_eq_meromorphicOrderAt ha]
        exact (hv i).2.2.1 x
  · intro x hx hxq
    rw [hloc]
    exact Finset.analyticAt_sum Finset.univ (fun i _ => analyticAt_const.smul
      ((hv i).2.2.2 x hxq (fun he => hx (he ▸ i.property))))

/-- Source: Forster, Lectures on Riemann Surfaces, §18, regular representatives of third-kind differentials. -/
theorem thirdKindDifferential_supported_on_divisor
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (p : C) (D : C →₀ ℤ)
    (hdeg : b4c_deg D = 0) :
    ∃ w : b4c_MeroForm E C h,
      (∀ x, b4c_res (hE := h) w x = (D x : ℂ)) ∧
      (∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0) ∧
      ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0 := by
  obtain ⟨w, hres, ho, q, hq, ha⟩ := thirdKindDifferential_of_degree_zero h p D hdeg
  have hregular (x : C) (hx : x ∉ D.support) :
      0 ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0 := by
    have hr : residue (HurwitzPrymRR_loc h w x) 0 = 0 := by
      change b4c_res (hE := h) w x = 0
      rw [hres, Finsupp.notMem_support_iff.mp hx, Int.cast_zero]
    obtain ⟨g, hg, he⟩ :=
      (RiemannRochEichler_simple_pole_removable (w.property.2 x) (ho x)).mp hr
    rw [meromorphicOrderAt_congr he]
    exact hg.meromorphicOrderAt_nonneg
  obtain ⟨v, he, hv, _⟩ := RiemannRochEichler_regularize_off_poles h w
    (D.support : Set C) hregular
  refine ⟨v, ?_, ?_, hv⟩
  · intro x
    exact (residue_congr_nhdsNE (he x)).trans (hres x)
  · intro x
    rw [meromorphicOrderAt_congr (he x)]
    exact ho x

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour

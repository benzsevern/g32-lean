import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemClusters
import HodgeLean.Foundations.Program.SchoenCyclePairedEvaluation
import HodgeLean.Foundations.Program.SchoenCycleGenusTransport

/-! # Evaluation of full-system divisor clusters -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
  [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] (k s : ℕ)
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)
variable
  (y : Fin (2 * s) → ComplexPoint Z) (hy : Function.Injective y)
  (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
  (hW : ∀ q : W, b4c_IsMeroForm hOne q.val ∧
    (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hOne q.val p) 0) ∧
    (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hOne q.val p) 0) ∧
    ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
  (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * s)
  (γ : g3_power Z (2 * k) ⟶ B) (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "F₀" => (residualProjectiveSystemPoint hOne y hy W hW hgenus γ id)
include hy hW hgenus hγ


/-- Exact full-system clusters evaluate in the actual supplied symmetric quotient. -/
theorem residual_system_quotient_eq_clusters
    (v : W) (hv : v ≠ 0) {ι : Type} [Fintype ι] (d : ι → ℕ)
    (e : Fin (2 * k) ≃ ((i : ι) × Fin (d i)))
    (f : (i : ι) → Fin (d i) → ComplexPoint Z)
    (hdiv : (b4c_divForm (hE := hOne) v.val + s2e_markedPoleDivisor y) =
      ∑ i, ∑ j, Finsupp.single (f i j) (1 : ℤ)) :
    F₀ (Projectivization.mk ℂ v hv) =
      Point.map γ (s2_lift (2 * k) (fun j => f (e j).1 (e j).2)) := by
  classical
  unfold residualProjectiveSystemPoint
  apply s2e_symmetricQuotientEvaluation_eq (2 * k) γ hγ _ _
  rw [Sym.map_id]
  change (List.ofFn (fun j => f (e j).1 (e j).2) : Multiset (ComplexPoint Z)) =
    s2e_divisorSym (residualProjectiveDivisor hOne y W (Projectivization.mk ℂ v hv)) _ _
  apply s2e_divisor_tuple_enumeration
  change (b4c_divForm (hE := hOne) v.val + s2e_markedPoleDivisor y) = _
  rw [hdiv]
  simpa only [Fintype.sum_sigma] using
    (e.sum_comp (fun t : (i : ι) × Fin (d i) => Finsupp.single (f t.1 t.2) (1 : ℤ))).symm
#print axioms residual_system_quotient_eq_clusters
/-- Full-system cluster charts evaluate all nearby projective divisor parameters. -/
theorem residual_system_centred_cluster_evaluation
    {m : ℕ} (b : Fin m → W)
    (a : Fin m → ℂ) (hne : (∑ j, a j • b j : W) ≠ 0) :

    let D := (b4c_divForm (hE := hOne) (∑ j, a j • b j : W).val + s2e_markedPoleDivisor y)
    ∃ (d : D.support → ℕ) (c : (i : D.support) → Fin (d i) → (Fin m → ℂ) → ℂ)
      (e : Fin (2 * k) ≃ ((i : D.support) × Fin (d i))),
      (∀ i j, AnalyticAt ℂ (c i j) a) ∧ (∀ i j, c i j a = 0) ∧
      ∀ᶠ a' in nhds a, ∃ hn : (∑ j, a' j • b j : W) ≠ 0,
        ∀ z : (i : D.support) → Fin (d i) → ℂ,
          (∀ i, monicPoly (c i) a' = ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
          residualProjectiveSystemPoint hOne y hy W hW hgenus γ id (Projectivization.mk ℂ (∑ j, a' j • b j : W) hn) =
            Point.map γ (s2_lift (2 * k) (fun k =>
              (extChartAt 𝓘(ℂ, Fin 1 → ℂ) ((e k).1 : ComplexPoint Z)).symm
                (extChartAt 𝓘(ℂ, Fin 1 → ℂ) ((e k).1 : ComplexPoint Z) ((e k).1 : ComplexPoint Z) +
                  b4cov_lineEquiv hOne (z (e k).1 (e k).2)))) := by
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z

  let D := (b4c_divForm (hE := hOne) (∑ j, a j • b j : W).val + s2e_markedPoleDivisor y)
  obtain ⟨d, r, δ, c, hd, hr, ht, hc, hc0, he⟩ :=
    residual_system_centred_support_divisor_presentation hOne y hy W hW k hgenus b a hne
  have hsum : (∑ i, d i) = (2 * k) := by
    have hi : ((∑ i, d i : ℕ) : ℤ) = ((2 * k) : ℤ) := by
      rw [Nat.cast_sum]
      calc
        (∑ i, (d i : ℤ)) = ∑ i : D.support, D i :=
          Finset.sum_congr rfl (fun i _ => hd i)
        _ = b4c_deg D := by simp [b4c_deg, Finsupp.sum, Finset.sum_attach]
        _ = ((2 * k) : ℤ) := residualProjectiveDivisor_degree hOne y W
          (fun q => ⟨(hW q).1, (hW q).2.2⟩) hgenus (Projectivization.mk ℂ _ hne)
    exact_mod_cast hi
  let e : Fin (2 * k) ≃ ((i : D.support) × Fin (d i)) :=
    (Fintype.equivFinOfCardEq (show Fintype.card ((i : D.support) × Fin (d i)) = (2 * k) by
      simpa only [Fintype.card_sigma, Fintype.card_fin] using hsum)).symm
  refine ⟨d, c, e, fun i j => hc i j a (Metric.mem_ball_self (hr i).2), hc0, ?_⟩
  filter_upwards [he] with a' ha'
  refine ⟨ha'.1, fun z hz => ?_⟩
  exact residual_system_quotient_eq_clusters Z B k s y hy W hW hgenus γ hγ _ ha'.1 d e
    (fun i j => (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (i : ComplexPoint Z)).symm
      (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (i : ComplexPoint Z) (i : ComplexPoint Z) +
        b4cov_lineEquiv hOne (z i j))) (ha'.2 z hz).2

#print axioms residual_system_centred_cluster_evaluation
/-- Every finite full-system linear chart has an analytic evaluation graph. -/
theorem residual_system_chart_graph_analytic
    (q : ℕ) [SmoothOfRelativeDimension q B.hom]
    {m : ℕ} (b : Fin m → W)
    (a : Fin m → ℂ) (hne : (∑ j, a j • b j) ≠ 0) :
    let Q := residualProjectiveSystemPoint hOne y hy W hW hgenus γ id (Projectivization.mk ℂ (∑ j, a j • b j) hne)
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {ty : (Fin m → ℂ) × (Fin q → ℂ) |
        ∃ hn : (∑ j, (a + ty.1) j • b j) ≠ 0,
          localChart B q Q (residualProjectiveSystemPoint hOne y hy W hW hgenus γ id
            (Projectivization.mk ℂ (∑ j, (a + ty.1) j • b j) hn)) = ty.2}
      (0, localChart B q Q Q) := by
  let Q := residualProjectiveSystemPoint hOne y hy W hW hgenus γ id (Projectivization.mk ℂ (∑ j, a j • b j) hne)

  let D := (b4c_divForm (hE := hOne) (∑ j, a j • b j : W).val + s2e_markedPoleDivisor y)
  obtain ⟨d, c, e, hc, hc0, he⟩ := residual_system_centred_cluster_evaluation Z B k s y hy W hW hgenus γ hγ b a hne
  let V := (i : D.support) → Fin (d i) → ℂ
  let p : Fin (2 * k) → ComplexPoint Z := fun k => (e k).1
  let L : V →L[ℂ] (Fin (2 * k) → ℂ) := ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (e k).2 : (Fin (d (e k).1) → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj (e k).1)
  let F : V → (Fin q → ℂ) := fun z => localChart B q Q
    (Point.map γ (s2_lift (2 * k) (fun k =>
      (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k)).symm
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k) (p k) + b4cov_lineEquiv hOne (L z k)))))
  have hz0 : ∀ i, monicPoly (c i) a =
      ∏ j, (Polynomial.X - Polynomial.C ((0 : V) i j)) := by
    intro i
    simp [monicPoly, hc0, V]
  have hQ : Q = Point.map γ (s2_lift (2 * k) p) := by
    obtain ⟨hn, hh⟩ := he.self_of_nhds
    simpa only [Pi.zero_apply, map_zero, add_zero, extChartAt_to_inv] using hh 0 hz0
  have hF : AnalyticAt ℂ F 0 := by
    have hh := s2e_curve_tuple_evaluation_chart_analytic Z B (2 * k) q γ p L
    rw [← hQ] at hh
    exact hh
  have hF0 : F 0 = localChart B q Q Q := by
    simp only [F, map_zero, Pi.zero_apply, add_zero, extChartAt_to_inv]
    rw [← hQ]
  let c' := fun i j t => c i j (a + t)
  have hc' : ∀ i j, AnalyticAt ℂ (c' i j) 0 := by
    intro i j
    exact (hc i j).comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero a)
  have hc0' : ∀ i j, c' i j 0 = 0 := by
    intro i j
    simpa only [c', add_zero] using hc0 i j
  have hrel := s2e_monic_cluster_evaluation_relation_analytic d c' hc' hc0' F hF
  rw [hF0] at hrel
  apply hrel.congr
  have het : ∀ᶠ t : Fin m → ℂ in nhds 0, ∃ hn : (∑ j, (a + t) j • b j) ≠ 0,
      ∀ z : V, (∀ i, monicPoly (c i) (a + t) =
        ∏ j, (Polynomial.X - Polynomial.C (z i j))) →
      residualProjectiveSystemPoint hOne y hy W hW hgenus γ id (Projectivization.mk ℂ (∑ j, (a + t) j • b j) hn) =
        Point.map γ (s2_lift (2 * k) (fun k =>
          (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k)).symm
            (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k) (p k) + b4cov_lineEquiv hOne (L z k)))) := by
    have ht : Tendsto (fun t : Fin m → ℂ => a + t) (nhds 0) (nhds a) := by
      simpa only [add_zero] using
        (show Continuous (fun t : Fin m → ℂ => a + t) from continuous_const.add continuous_id).tendsto
          (0 : Fin m → ℂ)
    exact ht.eventually he
  have hey := (continuous_fst.tendsto (0, localChart B q Q Q)).eventually het
  filter_upwards [hey] with ty hty
  obtain ⟨hn, hval⟩ := hty
  constructor
  · rintro ⟨z, hz, hy⟩
    refine ⟨hn, ?_⟩
    rw [hval z hz]
    exact hy
  · rintro ⟨hn', hy⟩
    obtain ⟨z, hz⟩ := (s2e_monic_cluster_rootTuples_finite_nonempty d c' ty.1).2
    refine ⟨z, hz, ?_⟩
    rw [hval z hz] at hy
    exact hy

#print axioms residual_system_chart_graph_analytic
/-- Nearby full-system divisor evaluations vary continuously in every linear chart. -/
theorem residual_system_evaluation_continuousAt
    {m : ℕ} (b : Fin m → W)
    (a : Fin m → ℂ) (hne : (∑ j, a j • b j) ≠ 0)
    (g : (Fin m → ℂ) → ComplexPoint B)
    (hge : ∀ᶠ a' in nhds a, ∃ hn : (∑ j, a' j • b j) ≠ 0,
      g a' = residualProjectiveSystemPoint hOne y hy W hW hgenus γ id
        (Projectivization.mk ℂ (∑ j, a' j • b j) hn)) : ContinuousAt g a := by

  let D := (b4c_divForm (hE := hOne) (∑ j, a j • b j : W).val + s2e_markedPoleDivisor y)
  obtain ⟨d, c, e, hc, hc0, he⟩ :=
    residual_system_centred_cluster_evaluation Z B k s y hy W hW hgenus γ hγ b a hne
  let V := (i : D.support) → Fin (d i) → ℂ
  let p : Fin (2 * k) → ComplexPoint Z := fun k => (e k).1
  let L : V →L[ℂ] (Fin (2 * k) → ℂ) := ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (e k).2 : (Fin (d (e k).1) → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj (e k).1)
  let F : V → ComplexPoint B := fun z => Point.map γ (s2_lift (2 * k) (fun k =>
    (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k)).symm
      (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p k) (p k) + b4cov_lineEquiv hOne (L z k))))
  have hF : ContinuousAt F 0 := s2e_curve_tuple_evaluation_continuousAt Z B (2 * k) γ p L
  let c' := fun i j t => c i j (a + t)
  have hc' : ∀ i j, ContinuousAt (c' i j) 0 := by
    intro i j
    exact (hc i j).continuousAt.comp_of_eq
      (continuousAt_const.add continuousAt_id) (add_zero a)
  have hc0' : ∀ i j, c' i j 0 = 0 := by
    intro i j
    simpa only [c', add_zero] using hc0 i j
  have ht : Tendsto (fun t : Fin m → ℂ => a + t) (nhds 0) (nhds a) := by
    simpa only [add_zero] using
      (show Continuous (fun t : Fin m → ℂ => a + t) from continuous_const.add continuous_id).tendsto
        (0 : Fin m → ℂ)
  have htrans : ContinuousAt (fun t => g (a + t)) 0 := by
    apply s2e_monic_cluster_evaluation_continuousAt d c' hc' hc0' F hF
    filter_upwards [ht.eventually he, ht.eventually hge] with t he' hg'
    obtain ⟨hn, hval⟩ := he'
    obtain ⟨hn', hg'⟩ := hg'
    intro z hz
    exact (hval z hz).symm.trans hg'.symm
  have hh := htrans.comp_of_eq
    (show ContinuousAt (fun x : Fin m → ℂ => x - a) a from
      continuousAt_id.sub continuousAt_const) (sub_self a)
  change ContinuousAt (fun x => g (a + (x - a))) a at hh
  have heq : (fun x => g (a + (x - a))) = g := by
    funext x
    congr 1
    abel
  rwa [heq] at hh

#print axioms residual_system_evaluation_continuousAt
end HodgeLean.Foundations.Program.G32Native

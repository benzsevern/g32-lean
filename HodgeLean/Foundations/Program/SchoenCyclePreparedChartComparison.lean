import HodgeLean.Foundations.Program.SchoenCyclePreparedRootCoefficients
import HodgeLean.Foundations.Program.SchoenCyclePairedClusters
import HodgeLean.Foundations.Program.SchoenCycleIndexedLiftProjection

/-! # Exact comparison of prepared roots and retained block coefficients -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MvPolynomial
open Filter Topology Manifold HodgeLean.Adapters
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators ContDiff Classical
namespace HodgeLean.Foundations.Program

/-- Exact root-cluster evaluations identify the supplied prepared coefficients with the retained block chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_prepared_clusters_eq_retained_coefficients
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom] [SmoothOfRelativeDimension 1 Z.hom]
    (n b d : ℕ) (γ : g3_power Z n ⟶ B)
    (x : ComplexPoint (g3_power Z n)) (m : Fin b → ℕ)
    (ι : (Σ a, Fin (m a)) ≃ Fin n) (p : Fin b → ComplexPoint Z)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    (e : ComplexPoint B → Fin n → ℂ)
    (he : ∀ᶠ q in 𝓝 x, ∀ a (j : Fin (m a)),
      e (Point.map γ q) (ι ⟨a, j⟩) = (-1 : ℂ) ^ (m a - j.val) *
        aeval (fun i : Fin (m a) =>
          (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
            (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)
              (Point.map (g3_proj Z n (ι ⟨a, i⟩)) q) -
             extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a)))
          (esymm (Fin (m a)) ℂ (m a - j.val)))
    (c : (a : Fin b) → Fin (m a) → (Fin d → ℂ) → ℂ)
    (hc : ∀ a j, ContinuousAt (c a j) 0) (hc0 : ∀ a j, c a j 0 = 0)
    (β : (Fin d → ℂ) → ComplexPoint B)
    (hβ : ∀ᶠ t in 𝓝 (0 : Fin d → ℂ), ∀ z : (a : Fin b) → Fin (m a) → ℂ,
      (∀ a, monicPoly (c a) t = ∏ j, (Polynomial.X - Polynomial.C (z a j))) →
      Point.map γ (s2_lift n (fun i =>
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p (ι.symm i).1)).symm
          (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p (ι.symm i).1) (p (ι.symm i).1) +
            b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)
              (z (ι.symm i).1 (ι.symm i).2)))) = β t) :
    ∀ᶠ t in 𝓝 (0 : Fin d → ℂ), ∀ a j, c a j t = e (β t) (ι ⟨a, j⟩) := by
  let V := (a : Fin b) → Fin (m a) → ℂ
  let F : V → ComplexPoint (g3_power Z n) := fun z => s2_lift n (fun i =>
    (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p (ι.symm i).1)).symm
      (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p (ι.symm i).1) (p (ι.symm i).1) +
        b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)
          (z (ι.symm i).1 (ι.symm i).2)))
  let L : V →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.proj (ι.symm i).2 : (Fin (m (ι.symm i).1) → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj (ι.symm i).1 : V →L[ℂ] (Fin (m (ι.symm i).1) → ℂ))
  have hF : ContinuousAt F 0 := by
    change ContinuousAt (fun z : V => Point.map (𝟙 (g3_power Z n)) (F z)) 0
    exact s2e_curve_tuple_evaluation_continuousAt Z (g3_power Z n) n (𝟙 _) (fun i => p (ι.symm i).1) L
  have hF0 : F 0 = x := by
    change s2_lift n (fun i =>
      (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p (ι.symm i).1)).symm
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p (ι.symm i).1) (p (ι.symm i).1) +
          b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 0)) = x
    simp only [map_zero, add_zero, extChartAt_to_inv]
    rw [← s2e_lift_coordinates n x]
    congr 1
    funext i
    obtain ⟨⟨a, j⟩, rfl⟩ := ι.surjective i
    simpa only [Equiv.symm_apply_apply, Point.map] using (hx a j).symm
  have hnear : ∀ᶠ z in 𝓝 (0 : V), ∀ a (j : Fin (m a)),
      e (Point.map γ (F z)) (ι ⟨a, j⟩) = (-1 : ℂ) ^ (m a - j.val) *
        aeval (fun i : Fin (m a) =>
          (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
            (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)
              (Point.map (g3_proj Z n (ι ⟨a, i⟩)) (F z)) -
             extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a)))
          (esymm (Fin (m a)) ℂ (m a - j.val)) := by
    have ht := hF.tendsto
    rw [hF0] at ht
    exact ht.eventually he
  obtain ⟨δ, hδ, hnearδ⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  choose r hr hchart using fun a => s2e_curve_chart_disc_avoids_marked
    (Module.finrank_fin_fun (n := 1) ℂ) (Fin.elim0 : Fin 0 → ComplexPoint Z) (p a)
  have hsmall := s2e_monic_cluster_rootTuples_eventually_small m c hc hc0 hδ
  have hdiscs := eventually_all.mpr (fun a =>
    s2e_monic_rootTuples_eventually_small (c a) (hc a) (hc0 a) (hr a))
  filter_upwards [hβ, hsmall, hdiscs] with t ht hsmallt hdisct
  obtain ⟨z, hz⟩ := (s2e_monic_cluster_rootTuples_finite_nonempty m c t).2
  have hroot : ∀ a i, z a i ∈ Metric.ball (0 : ℂ) (r a) := by
    intro a i
    have hn := hdisct a (z a) (hz a)
    rw [dist_zero_right, pi_norm_lt_iff (hr a)] at hn
    simpa only [Metric.mem_ball, dist_zero_right] using hn i
  have heq := hnearδ z (hsmallt z hz)
  have hval : Point.map γ (F z) = β t := ht z hz
  intro a j
  have hco := heq a j
  have hcoord (i : Fin (m a)) :
      (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)
          (Point.map (g3_proj Z n (ι ⟨a, i⟩)) (F z)) -
          extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a)) = z a i := by
    have hpj : Point.map (g3_proj Z n (ι ⟨a, i⟩)) (F z) =
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)).symm
          (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a) +
            b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) (z a i)) := by
      change s2_lift n _ ≫ g3_proj Z n (ι ⟨a, i⟩) = _
      exact s2e_indexed_cluster_lift_projection m ι
        (fun a i => (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)).symm
          (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a) +
            b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) (z a i))) a i
    rw [hpj, (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)).right_inv
      (hchart a (z a i) (hroot a i)).1, add_sub_cancel_left,
      ContinuousLinearEquiv.symm_apply_apply]
  simp_rw [hcoord] at hco
  rw [hval] at hco
  exact (s2e_prepared_root_tuple_coefficients (c a) t (z a) (hz a) j).trans hco.symm

#print axioms s2e_prepared_clusters_eq_retained_coefficients
end HodgeLean.Foundations.Program

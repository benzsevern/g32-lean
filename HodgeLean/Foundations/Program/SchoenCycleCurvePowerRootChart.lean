import HodgeLean.Foundations.Program.SchoenCycleCanonicalFamily
import HodgeLean.Foundations.Program.SchoenCycleSymmetricPoints
import HodgeLean.Foundations.Program.SchoenCycleRRParameterEvaluation

/-! # Actual curve-power points in centred root coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open Filter Topology Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- Move every actual curve coordinate in its own centred native chart along the specified complex line equivalence.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Lemma 2.4, printed p. 15. -/
def s2e_curvePowerRootChart
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (n : ℕ)
    (x : ComplexPoint (g3_power Z n)) (L : ℂ ≃L[ℂ] (Fin 1 → ℂ))
    (z : Fin n → ℂ) : ComplexPoint (g3_power Z n) :=
  s2_lift n (fun i => (ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x)).symm
    (ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x)
      (Point.map (g3_proj Z n i) x) + L (z i)))

/-- Projection of an actual root-chart tuple is its specified native inverse-chart point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Lemma 2.4, printed p. 15. -/
theorem s2e_curvePowerRootChart_projection
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (n : ℕ)
    (x : ComplexPoint (g3_power Z n)) (L : ℂ ≃L[ℂ] (Fin 1 → ℂ))
    (z : Fin n → ℂ) (i : Fin n) :
    Point.map (g3_proj Z n i) (s2e_curvePowerRootChart Z n x L z) =
      (ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x)).symm
        (ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x)
          (Point.map (g3_proj Z n i) x) + L (z i)) :=
  s2_check_lift_proj n _ i

/-- The actual root chart sends the zero root vector to its specified retained tuple.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Lemma 2.4, printed p. 15. -/
theorem s2e_curvePowerRootChart_zero
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (n : ℕ)
    (x : ComplexPoint (g3_power Z n)) (L : ℂ ≃L[ℂ] (Fin 1 → ℂ)) :
    s2e_curvePowerRootChart Z n x L 0 = x := by
  apply s2e_power_hom_ext
  intro i
  change Point.map (g3_proj Z n i) (s2e_curvePowerRootChart Z n x L 0) =
    Point.map (g3_proj Z n i) x
  rw [s2e_curvePowerRootChart_projection]
  simp only [Pi.zero_apply, map_zero, add_zero]
  exact (ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x)).left_inv
    (ComplexPoint.mem_localChart_source Z 1 _)

/-- Small root vectors give actual tuples tending to the specified retained tuple, also at repeated coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Lemma 2.4, printed p. 15. -/
theorem s2e_curvePowerRootChart_tendsto
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z n)) (L : ℂ ≃L[ℂ] (Fin 1 → ℂ)) :
    Tendsto (s2e_curvePowerRootChart Z n x L) (𝓝 0) (𝓝 x) := by
  have hc : ContinuousAt (s2e_curvePowerRootChart Z n x L) 0 := by
    apply (s2e_projective_tuple_lift_continuous Z n).continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    let p := Point.map (g3_proj Z n i) x
    let C := ComplexPoint.localChart Z 1 p
    have hpC : p ∈ C.source := ComplexPoint.mem_localChart_source Z 1 p
    have ha : ContinuousAt (fun z : Fin n → ℂ => C p + L (z i)) 0 :=
      continuousAt_const.add (L.continuousAt.comp (continuous_apply i).continuousAt)
    exact (C.continuousAt_symm (C.map_source hpC)).comp_of_eq ha
      (by rw [Pi.zero_apply, map_zero, add_zero])
  simpa only [s2e_curvePowerRootChart_zero] using hc.tendsto

/-- Actual quotient evaluation of the root chart is analytic in the target's native coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Lemma 2.4, printed p. 15. -/
theorem s2e_curvePowerRootChart_map_analytic
    (Z B : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n d : ℕ) [SmoothOfRelativeDimension d B.hom] (f : g3_power Z n ⟶ B)
    (x : ComplexPoint (g3_power Z n)) :
    AnalyticAt ℂ (fun z => ComplexPoint.localChart B d (Point.map f x)
      (Point.map f (s2e_curvePowerRootChart Z n x
        (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)) z))) 0 := by
  have hp : s2_lift n (fun i => Point.map (g3_proj Z n i) x) = x :=
    s2e_lift_coordinates n x
  have h := s2e_curve_tuple_evaluation_chart_analytic Z B n d f
    (fun i => Point.map (g3_proj Z n i) x) (ContinuousLinearMap.id ℂ (Fin n → ℂ))
  simpa only [hp, ContinuousLinearMap.id_apply, s2e_curvePowerRootChart,
    s2e_native_curve_extChart_apply, s2e_native_curve_extChart_symm_apply] using h

/-- Near the centre, every actual root-chart coordinate lies in its native chart and recovers its original scalar root parameter.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Lemma 2.4, printed p. 15. -/
theorem s2e_curvePowerRootChart_coordinates
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (n : ℕ)
    (x : ComplexPoint (g3_power Z n)) (L : ℂ ≃L[ℂ] (Fin 1 → ℂ)) :
    ∀ᶠ z : Fin n → ℂ in 𝓝 0, ∀ i : Fin n,
      let p := Point.map (g3_proj Z n i) x
      let C := ComplexPoint.localChart Z 1 p
      Point.map (g3_proj Z n i) (s2e_curvePowerRootChart Z n x L z) ∈ C.source ∧
        L.symm (C (Point.map (g3_proj Z n i) (s2e_curvePowerRootChart Z n x L z)) - C p) = z i := by
  have ht (i : Fin n) : ∀ᶠ z : Fin n → ℂ in 𝓝 0,
      let p := Point.map (g3_proj Z n i) x
      let C := ComplexPoint.localChart Z 1 p
      C p + L (z i) ∈ C.target := by
    let p := Point.map (g3_proj Z n i) x
    let C := ComplexPoint.localChart Z 1 p
    have hc : Continuous (fun z : Fin n → ℂ => C p + L (z i)) :=
      continuous_const.add (L.continuous.comp (continuous_apply i))
    have hh : Tendsto (fun z : Fin n → ℂ => C p + L (z i)) (𝓝 0) (𝓝 (C p)) := by
      simpa only [Pi.zero_apply, map_zero, add_zero] using hc.tendsto 0
    exact hh (C.open_target.mem_nhds (C.map_source (ComplexPoint.mem_localChart_source Z 1 p)))
  filter_upwards [eventually_all.mpr ht] with z hz
  intro i
  dsimp only
  rw [s2e_curvePowerRootChart_projection]
  let p := Point.map (g3_proj Z n i) x
  let C := ComplexPoint.localChart Z 1 p
  refine ⟨C.symm.map_source (hz i), ?_⟩
  rw [C.right_inv (hz i)]
  have hv : C p + L (z i) - C p = L (z i) := by abel
  rw [hv, L.symm_apply_apply]

end HodgeLean.Foundations.Program

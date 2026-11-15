import Mathlib.Topology.Algebra.Group.ContinuousDiv
import HodgeLean.Foundations.Program.SchoenCycleMixedCoefficientRootChart
import HodgeLean.Foundations.Program.SchoenCycleLocalRightInverse

/-! # Actual quotient neighbourhood images in mixed root coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MvPolynomial
open HodgeLean.Adapters Filter Topology Manifold
open scoped ContDiff BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- An actual quotient coefficient chart with the exact mixed root equations has the full neighbourhood image at its retained tuple.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Lemma 2.4, printed p. 15. -/
theorem s2e_root_chart_quotient_map_nhds
    (Z B : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z n ⟶ B) (x : ComplexPoint (g3_power Z n))
    (b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (e : OpenPartialHomeomorph (ComplexPoint B) (Fin n → ℂ))
    (hy : Point.map γ x ∈ e.source) (he0 : e (Point.map γ x) = 0)
    (he : ∀ᶠ z : Fin n → ℂ in 𝓝 0, ∀ a (j : Fin (m a)),
      e (Point.map γ (s2e_curvePowerRootChart Z n x
        (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)) z)) (ι ⟨a, j⟩) =
        (-1 : ℂ) ^ (m a - j.val) * aeval (fun i => z (ι ⟨a, i⟩))
          (esymm (Fin (m a)) ℂ (m a - j.val))) :
    Filter.map (fun z => Point.map γ (s2e_curvePowerRootChart Z n x
      (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)) z)) (𝓝 0) =
        𝓝 (Point.map γ x) := by
  let L := b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)
  let Q := fun z => Point.map γ (s2e_curvePowerRootChart Z n x L z)
  have hQ : Tendsto Q (𝓝 0) (𝓝 (Point.map γ x)) :=
    (Point.continuous_map γ).continuousAt.tendsto.comp (s2e_curvePowerRootChart_tendsto Z n x L)
  have hQ0 : Q 0 = Point.map γ x := by
    dsimp only [Q]
    rw [s2e_curvePowerRootChart_zero]
  have hright := s2e_mixedCoefficientRootSelection_right_inverse m ι (fun z => e (Q z)) he
  exact s2e_map_nhds_eq_of_chart_right_inverse Q (s2e_mixedCoefficientRootSelection m ι)
    0 (Point.map γ x) 0 e hy he0 hQ0 hQ
    (s2e_mixedCoefficientRootSelection_tendsto_zero m ι) hright

/-- A full actual point-neighbourhood image remains full in centred native coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Lemma 2.4, printed p. 15. -/
theorem s2e_centered_native_chart_map_nhds
    (B : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d B.hom]
    (y : ComplexPoint B) {T : Type*} [TopologicalSpace T] (Q : T → ComplexPoint B) (t : T)
    (hmap : Filter.map Q (𝓝 t) = 𝓝 y) :
    Filter.map (fun z => ComplexPoint.localChart B d y (Q z) - ComplexPoint.localChart B d y y)
      (𝓝 t) = 𝓝 0 := by
  let C := ComplexPoint.localChart B d y
  change Filter.map ((Homeomorph.subRight (C y)) ∘ C ∘ Q) (𝓝 t) = 𝓝 0
  rw [← Filter.map_map, ← Filter.map_map, hmap,
    C.map_nhds_eq (ComplexPoint.mem_localChart_source B d y)]
  simpa only [Homeomorph.coe_subRight, sub_self] using (Homeomorph.subRight (C y)).map_nhds_eq (C y)

end HodgeLean.Foundations.Program

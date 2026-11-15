import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.SingularLocalContainment

/-! # Local constancy of multiplicity on a flattened support

Route: choose a connected tangential ball. For each algebraic component,
local containment of the support is equivalent to containment of that ball.
Thus every indicator in the frozen multiplicity sum is constant there.
-/
noncomputable section
namespace AlgebraicGeometry.SingularCycles
open CategoryTheory AlgebraicGeometry Set Filter Topology TopologicalSpace
open HodgeLean.Foundations.Analytic HodgeLean.Adapters
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Multiplicity is locally constant along any holomorphically flattened
cycle support, without a component codimension assumption.
Source: Fulton, Intersection Theory, second edition, §1.5; the analytic identity principle. -/
theorem singular_chart_multiplicity_locally_constant
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) {r c : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart q e)
    (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0)
    (x : ComplexPoint (Over.mk q)) (hx : x ∈ e.source) (hxS : x ∈ a3b4_cycleSupport q γ) :
    ∃ W : Opens (ComplexPoint (Over.mk q)), (W : Set _) ⊆ e.source ∧ x ∈ W ∧
      ∀ y ∈ W, y ∈ a3b4_cycleSupport q γ →
        a3b4_multiplicity q γ y = a3b4_multiplicity q γ x := by
  classical
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  let D := {t : Fin r → ℂ | (t, (0 : Fin c → ℂ)) ∈ e.target}
  have hD : IsOpen D := e.open_target.preimage (continuous_id.prodMk continuous_const)
  have hx0 := (hS x hx).mp hxS
  have hxD : (e x).1 ∈ D := by
    have heq : ((e x).1, (0 : Fin c → ℂ)) = e x := Prod.ext rfl hx0.symm
    change ((e x).1, (0 : Fin c → ℂ)) ∈ e.target
    rw [heq]
    exact e.map_source hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD (e x).1 hxD
  let V := Metric.ball (e x).1 ε
  let W : Opens (ComplexPoint (Over.mk q)) :=
    ⟨e.source ∩ e ⁻¹' (V ×ˢ (Set.univ : Set (Fin c → ℂ))),
      e.continuousOn.isOpen_inter_preimage e.open_source (Metric.isOpen_ball.prod isOpen_univ)⟩
  refine ⟨W, fun _ h => h.1, ⟨hx, Metric.mem_ball_self hε, Set.mem_univ _⟩, ?_⟩
  intro y hy hyS
  unfold a3b4_multiplicity
  apply Finset.sum_congr rfl
  intro ξ hξ
  have hA := f4_isClosedAnalytic_preimage (Over.mk q) (closure ({ξ} : Set Z)) isClosed_closure
  have hlocal := (singular_chart_localContainment (Over.mk q) e he
    (a3b4_cycleSupport q γ) (Point.underlying ⁻¹' closure ({ξ} : Set Z)) hS hA V
    Metric.isOpen_ball (convex_ball _ _).isPreconnected hball y hy.1 hyS hy.2.1).trans
      (singular_chart_localContainment (Over.mk q) e he
        (a3b4_cycleSupport q γ) (Point.underlying ⁻¹' closure ({ξ} : Set Z)) hS hA V
        Metric.isOpen_ball (convex_ball _ _).isPreconnected hball x hx hxS
        (Metric.mem_ball_self hε)).symm
  simp only [hlocal]

end AlgebraicGeometry.SingularCycles

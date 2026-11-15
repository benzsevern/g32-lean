import HodgeLean.Foundations.Program.G32Native.CanonicalAbelLiftOverlap
import HodgeLean.Foundations.Program.G32Native.LocalModelOverlap

/-! # Original local Abel lifts on actual ambient overlaps -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
open HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- The original local lifts agree in the original period quotient on overlaps.
Source: Bourbaki, General Topology, I §2, neighborhoods and local equality.
The coefficient lifts themselves may differ by a period. -/
theorem canonicalAbelLiftOverlap (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (hF : ∀ x : ComplexPoint G.Q,
      ∀ᶠ w in 𝓝 (Point.map G.ι x), ∀ z : Fin (2 * G.k) → ComplexPoint G.Z,
        Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w →
        canonicalPeriodQuotient G (canonicalChartAbelLift G F x w) =
          ∑ i, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z i)) :
    ∀ x : ComplexPoint G.Q, ∃ U : Set (ComplexPoint G.W),
      IsOpen U ∧ Point.map G.ι x ∈ U ∧
      ∀ y : ComplexPoint G.Q, Point.map G.ι y ∈ U →
        (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F x w))
          =ᶠ[𝓝 (Point.map G.ι y)]
        (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F y w)) := by
  intro x
  exact eventuallyEq_local_models_on_neighbourhood (Point.map G.ι)
    (fun x w => canonicalPeriodQuotient G (canonicalChartAbelLift G F x w))
    (canonicalAbelValue G p)
    (fun x => canonicalAbelValue_eventually_lift G p F x (hF x)) x

#print axioms canonicalAbelLiftOverlap
end HodgeLean.Foundations.Program.G32Native

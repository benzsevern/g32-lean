import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDifferentialDefs
import HodgeLean.Foundations.Program.SchoenPowerComplexPoints

/-! # The original Abel sum over the actual symmetric quotient fibres -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.AbelAdapter
open Filter Topology
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- Each original ambient quotient point has a representative by an
actual tuple of the original curve points under the specified quotient map. -/
theorem canonicalAbelTuple_preimage (G : CanonicalAbelGeometry) (w : ComplexPoint G.W) :
    ∃ z : Fin (2 * G.k) → ComplexPoint G.Z,
      Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w := by
  obtain ⟨y, hy⟩ := G.surjectiveγ (Point.map G.β w)
  refine ⟨s2_powerComplexPointEquiv G.Z (2 * G.k) y, ?_⟩
  change Point.map G.γ ((s2_powerComplexPointEquiv G.Z (2 * G.k)).symm
    (s2_powerComplexPointEquiv G.Z (2 * G.k) y)) = _
  rw [Equiv.symm_apply_apply]
  exact hy

/-- The original Abel sum of a chosen actual tuple representing the
specified original ambient quotient point. -/
def canonicalAbelValue (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (w : ComplexPoint G.W) : b3_Jacobian (Fin 1 → ℂ) (ComplexPoint G.Z) :=
  ∑ j : Fin (2 * G.k), analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p
    (Classical.choose (canonicalAbelTuple_preimage G w) j)

/-- The original quotient normalization identifies each specified local
Abel lift with the actual Abel sum of the representing original curve tuple. -/
theorem canonicalAbelValue_eventually_lift (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q)
    (h : ∀ᶠ w in 𝓝 (Point.map G.ι x), ∀ z : Fin (2 * G.k) → ComplexPoint G.Z,
      Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w →
      canonicalPeriodQuotient G (F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
        ∑ j, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z j)) :
    (fun w => canonicalPeriodQuotient G
      (F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w))) =ᶠ[𝓝 (Point.map G.ι x)]
      canonicalAbelValue G p := by
  filter_upwards [h] with w hw
  exact hw (Classical.choose (canonicalAbelTuple_preimage G w))
    (Classical.choose_spec (canonicalAbelTuple_preimage G w))

#print axioms canonicalAbelValue_eventually_lift
#print axioms canonicalAbelValue
#print axioms canonicalAbelTuple_preimage
end HodgeLean.Foundations.Program.G32Native

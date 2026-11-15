import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalOrientationDegree
import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

/-! # Specified complex orientations in the original middle cap degrees
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The original all-chart complex normalization retains the specified chart class after the original middle cap degree transport and any equal complex chart dimension.
Source: properCycle_local_orientation_degree; localClassOfChart.
HC no distance; AV milestone no distance. -/
lemma properCycle_complex_orientation_degree
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (k : ℕ)
    (c : Homology ℚ (a3b4_an X.hom) (2*(2*k)))
    (hcomplex : ∀ (e : OpenPartialHomeomorph (ComplexPoint X) (Fin (2*k) → ℂ)),
      (∀ i, (f4_analytification X).IsHolFun (fun z : e.source => e z i)) →
      ∀ (x : ComplexPoint X) (hx : x ∈ e.source),
        localOrientation (a3b4_an X.hom) (2*(2*k)) c x = localClassOfChart (2*k) e x hx)
    (n : ℕ) (hn : n = 2*k) (e : OpenPartialHomeomorph (ComplexPoint X) (Fin n → ℂ))
    (he : ∀ i, (f4_analytification X).IsHolFun (fun z : e.source => e z i))
    (x : ComplexPoint X) (hx : x ∈ e.source) :
    localOrientation (a3b4_an X.hom) (2*k+2*k)
      ((eqToIso (congrArg (fun j => Homology ℚ (a3b4_an X.hom) j)
        (show 2*(2*k) = 2*k+2*k by omega))).hom.hom c) x =
    (eqToIso (congrArg (fun j => orientationGroup (a3b4_an X.hom) j x)
      (show 2*n = 2*k+2*k by omega))).hom.hom (localClassOfChart n e x hx) := by
  subst n
  rw [properCycle_local_orientation_degree (a3b4_an X.hom) (2*(2*k)) (2*k+2*k)
    (by omega) c x, hcomplex e he x hx]

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.AlgebraicGeometry.ConormalFramesDefs
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import HodgeLean.Foundations.AlgebraicGeometry.ConormalFlatComparisonProofs
import HodgeLean.Foundations.AlgebraicGeometry.ConormalBaseChangeTransport

/-! # Cartesian comparison for the actual conormal sheaf
The square uses the original kernel-ideal and pullback objects.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Conormal

/-- Flat cartesian comparison for the conormal of an immersion.
Source: Hartshorne, Algebraic Geometry, II.8, conormal sequence and flat base change;
Stacks Project, Section 29.32, Lemma 29.32.4 (Tag 01R1). Independent open-restriction example: ConormalFramesChecks. -/
def flatBaseChangeIso_aux
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) [Flat f] (g : Q' ⟶ Q)
    (sq : IsPullback g i' i f) :
    (Scheme.Modules.pullback g).obj (sheaf i) ≅ sheaf i' := by
  have : IsIso (idealPullbackMap i i' f g sq.w) :=
    idealPullbackMap_isIso_of_flat i i' f g sq
  have : IsIso (comparisonMap i i' f g sq.w) :=
    comparisonMap_isIso_of_idealPullbackMap_isIso i i' f g sq.w
  exact asIso (comparisonMap i i' f g sq.w)

end AlgebraicGeometry.Conormal

import HodgeLean.Foundations.AlgebraicGeometry.ConormalBaseChangeProofs

/-! # Flat and etale conormal comparisons
The etale interface specializes the flat cartesian comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Conormal

/-- Flat cartesian comparison using the actual conormal sheaves.
Source: Hartshorne, Algebraic Geometry, II.8; Stacks Project, Section 29.32, Lemma 29.32.4 (Tag 01R1).
Independent open-restriction example: ConormalFramesChecks. -/
def flatBaseChangeIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) [Flat f] (g : Q' ⟶ Q)
    (sq : IsPullback g i' i f) :
    (Scheme.Modules.pullback g).obj (sheaf i) ≅ sheaf i' :=
  flatBaseChangeIso_aux i i' f g sq

/-- Etale cartesian comparison using flatness of the ambient map.
Source: Hartshorne, Algebraic Geometry, II.8; EGA IV, 17.1.1.
Independent open-restriction example: ConormalFramesChecks. -/
def etaleBaseChangeIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) [Etale f] (g : Q' ⟶ Q)
    (sq : IsPullback g i' i f) :
    (Scheme.Modules.pullback g).obj (sheaf i) ≅ sheaf i' :=
  flatBaseChangeIso i i' f g sq

end AlgebraicGeometry.Conormal

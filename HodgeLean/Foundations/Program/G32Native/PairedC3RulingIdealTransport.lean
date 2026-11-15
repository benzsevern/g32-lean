import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedMarkedRuling

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Transport a marked ruling along equality of its actual residual ideals. -/
theorem paired_ruling_of_ideal_eq
    {base : Scheme.{0}} {P V C : Over base} (i : P ⟶ V)
    (J J' : V.left.IdealSheafData) (h : J = J')
    (c₀ : base ⟶ C.left)
    (H : ∃ g : residualComponent (V := V) J ⟶ C,
      Smooth g.left ∧ IsPullback (residualIntersection i J).hom
        (residualIntersectionSecond i J).left c₀ g.left) :
    ∃ g : residualComponent (V := V) J' ⟶ C,
      Smooth g.left ∧ IsPullback (residualIntersection i J').hom
        (residualIntersectionSecond i J').left c₀ g.left := by
  subst J'
  exact H

#print axioms paired_ruling_of_ideal_eq
end HodgeLean.Foundations.Program.G32Native

import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Noetherian.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An actual fixed-function algebra inside a finite algebra remains finite over a Noetherian scalar ring.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 7. -/
theorem s2e_fixed_algebra_module_finite
    (A C G : Type*) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Module.Finite A C] [Group G] [MulSemiringAction G C] [SMulCommClass G A C] :
    Module.Finite A (FixedPoints.subalgebra A C G) :=
  Module.Finite.of_injective (FixedPoints.subalgebra A C G).val.toLinearMap Subtype.val_injective

#print axioms s2e_fixed_algebra_module_finite
end HodgeLean.Foundations.Program

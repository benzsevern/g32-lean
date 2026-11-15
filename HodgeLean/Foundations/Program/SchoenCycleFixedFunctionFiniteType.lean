import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Adjoin.Tower

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual fixed-function subalgebra of a finite group acting on an affine algebra of finite type is itself of finite type.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 7.8. -/
theorem s2e_fixed_function_finiteType
    (k C G : Type*) [CommRing k] [IsNoetherianRing k] [CommRing C] [Algebra k C]
    [Algebra.FiniteType k C] [Group G] [Finite G]
    [MulSemiringAction G C] [SMulCommClass G k C] :
    Algebra.FiniteType k (FixedPoints.subalgebra k C G) := by
  let S := FixedPoints.subalgebra k C G
  letI : Algebra.IsIntegral S C := Algebra.IsInvariant.isIntegral S C G
  letI : Algebra.FiniteType S C := Algebra.FiniteType.of_restrictScalars_finiteType k S C
  letI : Module.Finite S C := Algebra.IsIntegral.finite
  exact ⟨fg_of_fg_of_fg k S C Algebra.FiniteType.out Module.Finite.fg_top Subtype.val_injective⟩

#print axioms s2e_fixed_function_finiteType
end HodgeLean.Foundations.Program

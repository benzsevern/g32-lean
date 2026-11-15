import HodgeLean.Foundations.Program.SchoenInvariantRings
import Mathlib.RingTheory.Adjoin.Tower

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finite-group invariants in a finite-type algebra over a Noetherian ring form a finite-type algebra. -/
theorem s2_fixedAlgebra_finiteType (R B G : Type) [CommRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B] :
    Algebra.FiniteType R (FixedPoints.subalgebra R B G) := by
  haveI : Module.Finite (FixedPoints.subalgebra R B G) B := s2_fixedAlgebra_finite R B G
  exact ⟨fg_of_fg_of_fg R (FixedPoints.subalgebra R B G) B
    Algebra.FiniteType.out Module.Finite.fg_top Subtype.val_injective⟩

end HodgeLean.Foundations.Program

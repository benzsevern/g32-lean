import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential TensorProduct
namespace HodgeLean.Foundations.Program

/-- The differential fibre of a standard smooth algebra retains its relative dimension after formally étale localization.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.11.1; Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_smooth_differential_fibre_finrank
    (R S T K : Type*) [CommRing R] [CommRing S] [Nontrivial S] [CommRing T] [Field K]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra T K] [Algebra S K] [IsScalarTower S T K]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.FormallyEtale S T] :
    Module.finrank K (TensorProduct T K Ω[T⁄R]) = n := by
  letI : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let E := ((tensorKaehlerEquivOfFormallyEtale R S T).symm.baseChange T K _ _).trans
    (AlgebraTensorModule.cancelBaseChange S T K K Ω[S⁄R])
  rw [E.finrank_eq, Module.finrank_baseChange]
  simpa only [Module.finrank, Cardinal.toNat_natCast] using congrArg Cardinal.toNat
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := S) n)

#print axioms s2e_smooth_differential_fibre_finrank
end HodgeLean.Foundations.Program

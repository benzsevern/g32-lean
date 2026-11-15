import HodgeLean.Foundations.TubularEuler.SmoothConormalPointDifferentialHelpers
import HodgeLean.Foundations.TubularEuler.LocalizationDifferentialSquareHelpers

/-! # The smooth conormal injection detects localized square errors

The universal differential and its original split injection retain the
specified immersion ideal and both scalar extensions.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

theorem smoothConormalTensor_generator_zero_of_local_square
    {R A B K S : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K] [CommRing S]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra A K] [Algebra A S] [IsLocalRing S]
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R B]
    (hf : Function.Surjective (algebraMap A B))
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime S p]
    (hp : RingHom.ker (algebraMap A K) = p)
    (u : RingHom.ker (algebraMap A B)) (hu : algebraMap A K u.val = 0)
    (hsq : algebraMap A S u.val ∈ IsLocalRing.maximalIdeal S ^ 2) :
    (1 : K) ⊗ₜ[A] (RingHom.ker (algebraMap A B)).toCotangent u = 0 := by
  apply smoothConormalTensor_injective (R := R) (C := K) hf
  rw [universalPointDifferential_conormal_generator, map_zero]
  exact differential_zero_of_local_maximal_square p (algebraMap A K) hp
    (universalPointDifferential R A B K) (universalPointDifferential_leibniz R A B K)
    u.val hu hsq

#print axioms smoothConormalTensor_generator_zero_of_local_square

end HodgeLean.Foundations.TubularEuler

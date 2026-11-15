import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Unramified.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential
namespace HodgeLean.Foundations.Program

/-- The cotangent space of the kernel of an algebra augmentation maps onto the differential fibre over that augmentation.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8, the conormal sequence. -/
theorem s2e_augmentation_cotangent_differential_surjective
    (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    (ε : A →ₐ[k] k) :
    letI : Algebra A k := ε.toAlgebra
    Function.Surjective (kerCotangentToTensor k A k) := by
  letI : Algebra A k := ε.toAlgebra
  letI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq' ε.comp_algebraMap.symm
  have hε : Function.Surjective (algebraMap A k) := by
    intro c
    exact ⟨algebraMap k A c, ε.commutes c⟩
  intro x
  apply (exact_kerCotangentToTensor_mapBaseChange k A k hε x).mp
  exact Subsingleton.elim _ _

#print axioms s2e_augmentation_cotangent_differential_surjective
end HodgeLean.Foundations.Program

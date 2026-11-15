import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scalar extension of the smooth conormal injection

The algebraic conormal map has a linear retraction, so scalar extension
preserves its injectivity without a flatness assumption on the scalar ring.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
variable [Algebra A C] [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R B]

theorem smoothConormalTensor_injective
    (hf : Function.Surjective (algebraMap A B)) :
    Function.Injective (TensorProduct.AlgebraTensorModule.lTensor C C
      (KaehlerDifferential.kerCotangentToTensor R A B)) := by
  obtain ⟨l, hl⟩ :=
    (Algebra.FormallySmooth.iff_split_injection (R := R) (P := A) (A := B) hf).mp
      (inferInstance : Algebra.FormallySmooth R B)
  have hleft :
      (TensorProduct.AlgebraTensorModule.lTensor C C l).comp
        (TensorProduct.AlgebraTensorModule.lTensor C C
          (KaehlerDifferential.kerCotangentToTensor R A B)) = LinearMap.id := by
    rw [← TensorProduct.AlgebraTensorModule.lTensor_comp, hl,
      TensorProduct.AlgebraTensorModule.lTensor_id]
  exact (show Function.LeftInverse
    (TensorProduct.AlgebraTensorModule.lTensor C C l)
    (TensorProduct.AlgebraTensorModule.lTensor C C
      (KaehlerDifferential.kerCotangentToTensor R A B)) from
        fun t => LinearMap.congr_fun hleft t).injective

#print axioms smoothConormalTensor_injective

end HodgeLean.Foundations.TubularEuler

import HodgeLean.Foundations.TubularEuler.SmoothConormalTensorHelpers

/-! # The universal differential in the original conormal tensor target

The additive map retains both scalar extensions in the algebraic conormal
injection. HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

variable (R A B C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra A B] [Algebra A C]

def universalPointDifferential : A →+ C ⊗[A] (B ⊗[A] Ω[A⁄R]) :=
  ((TensorProduct.mk A C (B ⊗[A] Ω[A⁄R]) 1).comp
    (TensorProduct.mk A B Ω[A⁄R] 1)).toAddMonoidHom.comp
      (KaehlerDifferential.D R A).toAddMonoidHom

theorem universalPointDifferential_leibniz (a b : A) :
    universalPointDifferential R A B C (a * b) =
      algebraMap A C a • universalPointDifferential R A B C b +
        algebraMap A C b • universalPointDifferential R A B C a := by
  let F := (TensorProduct.mk A C (B ⊗[A] Ω[A⁄R]) 1).comp
    (TensorProduct.mk A B Ω[A⁄R] 1)
  change F ((KaehlerDifferential.D R A) (a * b)) =
    algebraMap A C a • F ((KaehlerDifferential.D R A) b) +
      algebraMap A C b • F ((KaehlerDifferential.D R A) a)
  rw [Derivation.leibniz, map_add, map_smul, map_smul]
  simp only [IsScalarTower.algebraMap_smul]

theorem universalPointDifferential_conormal_generator
    (u : RingHom.ker (algebraMap A B)) :
    TensorProduct.AlgebraTensorModule.lTensor C C
      (KaehlerDifferential.kerCotangentToTensor R A B)
      ((1 : C) ⊗ₜ[A] (RingHom.ker (algebraMap A B)).toCotangent u) =
        universalPointDifferential R A B C u.val := rfl

#print axioms universalPointDifferential_conormal_generator

#print axioms universalPointDifferential
#print axioms universalPointDifferential_leibniz

end HodgeLean.Foundations.TubularEuler

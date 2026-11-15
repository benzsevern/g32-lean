import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # The algebraic conormal comparison for a quotient tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

variable {K A B C : Type*} [CommRing K] [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower K A B] [IsScalarTower K A C] [IsScalarTower K B C]
    [IsScalarTower A B C]

/-- The quotient presentation retains the existing algebra structures,
so its cotangent tensor products use the original scalar actions.
Source: Hartshorne, Algebraic Geometry, II.8.12, ideal form. -/
def pairedC3QuotientPresentation (hAB : Function.Surjective (algebraMap A B)) :
    Algebra.Extension K B where
  Ring := A
  commRing := inferInstance
  algebra₁ := inferInstance
  algebra₂ := inferInstance
  isScalarTower := inferInstance
  σ b := (hAB b).choose
  algebraMap_σ b := (hAB b).choose_spec

/-- Identity on the ambient algebra induces the natural extension map
from the intermediate quotient presentation to the final presentation.
Source: Hartshorne, Algebraic Geometry, II.8.12, ideal form. -/
def pairedC3TowerExtensionMap
    (hAB : Function.Surjective (algebraMap A B))
    (hAC : Function.Surjective (algebraMap A C)) :
    Algebra.Extension.Hom
      (pairedC3QuotientPresentation (K := K) hAB)
      (pairedC3QuotientPresentation (K := K) hAC) where
  toRingHom := RingHom.id A
  toRingHom_algebraMap := by intro t; rfl
  algebraMap_toRingHom := by
    intro t
    exact IsScalarTower.algebraMap_apply A B C t

#print axioms pairedC3QuotientPresentation
#print axioms pairedC3TowerExtensionMap
end HodgeLean.Foundations.Program.G32Native

import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.RingTheory.Ideal.Maps

/-! # Ideal reduction in arbitrary surjective affine coordinates -/
noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Reduction of an ideal to its specified image ideal. -/
def unionConormalGeneralReduction
    {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    (I : Ideal R) (K : Ideal C) (hK : I.map (algebraMap R C) = K) : I →ₗ[R] K where
  toFun x := ⟨algebraMap R C x.val, hK ▸ Ideal.mem_map_of_mem _ x.property⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := by
    apply Subtype.ext
    change algebraMap R C (r * x.val) = r • algebraMap R C x.val
    rw [map_mul, Algebra.smul_def]

/-- The unit-tensor last map for arbitrary scalar coordinates. -/
def unionConormalGeneralLast
    {R B C D : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D] [Algebra B D] [Algebra C D]
    [IsScalarTower R B D] [IsScalarTower R C D]
    (I : Ideal R) (K : Ideal C) (hK : I.map (algebraMap R C) = K) :
    B ⊗[R] I →ₗ[B] D ⊗[C] K :=
  (((TensorProduct.mk C D K (1 : D)).restrictScalars R).comp
    (unionConormalGeneralReduction I K hK)).liftBaseChange B

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.UnionConormalGeneralMiddleExact
import HodgeLean.Foundations.Program.G32Native.UnionConormalGeneralSurjective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # The ideal tensor sequence with explicit ring maps -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The tensor reduction as a morphism over the first component ring. -/
def unionConormalRingLast
    {R B C D : Type} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    (q : R →+* B) (r : R →+* C) (s : C →+* D) (k : B →+* D)
    (hc : s.comp r = k.comp q)
    (hK : (RingHom.ker q).map r = RingHom.ker s) :
    (ModuleCat.extendScalars q).obj (ModuleCat.of R (RingHom.ker q)) ⟶
      (ModuleCat.restrictScalars k).obj
        ((ModuleCat.extendScalars s).obj (ModuleCat.of C (RingHom.ker s))) := by
  letI : Algebra R B := q.toAlgebra
  letI : Algebra R C := r.toAlgebra
  letI : Algebra B D := k.toAlgebra
  letI : Algebra C D := s.toAlgebra
  letI : Algebra R D := (s.comp r).toAlgebra
  letI : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' hc
  refine ModuleCat.ofHom
    (X := (ModuleCat.extendScalars q).obj (ModuleCat.of R (RingHom.ker q)))
    (Y := (ModuleCat.restrictScalars k).obj
      ((ModuleCat.extendScalars s).obj (ModuleCat.of C (RingHom.ker s)))) ?_
  change B ⊗[R] RingHom.ker q →ₗ[B] D ⊗[C] RingHom.ker s
  exact unionConormalGeneralLast (B := B) (D := D) _ _ hK

end HodgeLean.Foundations.Program.G32Native

import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.Complex.Basic

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι κ V W Z : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]

def m1b_multilinearFlip
    (f : MultilinearMap ℂ (fun _ : ι => V) (MultilinearMap ℂ (fun _ : κ => W) Z)) :
    MultilinearMap ℂ (fun _ : κ => W) (MultilinearMap ℂ (fun _ : ι => V) Z) where
  toFun w :=
    { toFun := fun v => f v w
      map_update_add' := by
        intro _ v i x y
        exact congrArg (fun g => g w) (f.map_update_add v i x y)
      map_update_smul' := by
        intro _ v i c x
        exact congrArg (fun g => g w) (f.map_update_smul v i c x) }
  map_update_add' := by
    intro _ w i x y
    apply MultilinearMap.ext
    intro v
    exact (f v).map_update_add w i x y
  map_update_smul' := by
    intro _ w i c x
    apply MultilinearMap.ext
    intro v
    exact (f v).map_update_smul w i c x

end HodgeLean.Foundations.Program

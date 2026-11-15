import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! Natural cokernel comparison for coefficient functors. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual cokernel comparison is natural in the defining arrow. -/
def persistenceCokernelCoefficientIso
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasCokernels C] [HasCokernels D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteColimits F] :
    (Limits.coker (C := C)) ⋙ F ≅ F.mapArrow ⋙ (Limits.coker (C := D)) :=
  NatIso.ofComponents (fun a => PreservesCokernel.iso F a.hom) (by
    intro a b f
    exact (preserves_cokernel_iso_comp_cokernel_map F a.hom b.hom
      f.left f.right f.w.symm).symm)

end HodgeLean.Foundations.QuotientDuality

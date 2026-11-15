import Mathlib.LinearAlgebra.TensorProduct.RightExactness

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The range of a scalar-extended linear map is the scalar extension of its range. -/
theorem s4_baseChange_range {K L V W : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (F : V →ₗ[K] W) : LinearMap.range (F.baseChange L) = (LinearMap.range F).baseChange L := by
  have he : F = (LinearMap.range F).subtype.comp F.rangeRestrict := rfl
  rw [he, LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top]
  · rfl
  · exact LinearMap.range_eq_top.mpr
      (LinearMap.baseChange_surjective L F.surjective_rangeRestrict)

end HodgeLean.Foundations.Program

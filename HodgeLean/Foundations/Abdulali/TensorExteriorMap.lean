import HodgeLean.Foundations.InvariantsExterior

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Abdulali

/-- The alternating quotient is natural for any linear map between vector spaces.
Source: the universal property of exterior powers. -/
theorem wedgeQuotient_naturality {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (n : ℕ) (f : V →ₗ[ℂ] W) (t : ⨂[ℂ]^n V) :
    exteriorPower.map n f (InvariantsExterior.wedgeQuotient n t) =
      InvariantsExterior.wedgeQuotient n (PiTensorProduct.map (fun _ => f) t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul, InvariantsExterior.wedgeQuotient_tprod,
      PiTensorProduct.map_tprod, exteriorPower.map_apply_ιMulti, Function.comp_def]
  | add a b ha hb => simp only [map_add, ha, hb]

end HodgeLean.Foundations.Abdulali

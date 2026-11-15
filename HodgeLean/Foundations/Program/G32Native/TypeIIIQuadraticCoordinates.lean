import HodgeLean.Foundations.WeilHermitian

noncomputable section
open HodgeLean.Foundations.WeilHermitian
namespace HodgeLean.Foundations.Program.G32Native

/-- Coordinates intertwining the quadratic generator give a quadratic linear
equivalence on the associated module. -/
def typeIIIQuadraticCoordinates
    {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    {a : ℚ} (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id})
    (F : V ≃ₗ[ℚ] (ι → QuadraticAlgebra ℚ a 0))
    (hF : ∀ v i, F (J.1 v) i = (⟨0, 1⟩ : QuadraticAlgebra ℚ a 0) * F v i) :
    WithJ V J ≃ₗ[QuadraticAlgebra ℚ a 0] (ι → QuadraticAlgebra ℚ a 0) where
  toFun v := F (WithJ.equiv J v)
  invFun x := (WithJ.equiv J).symm (F.symm x)
  left_inv v := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' z v := by
    apply funext
    intro i
    simp only [equiv_smul, map_add, map_smul, Pi.add_apply, Pi.smul_apply, hF,
      smul_eq_mul]
    rcases z with ⟨r, s⟩
    ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuadraticCoordinates

import HodgeLean.Foundations.AnalyticAlbanese.Basic

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.Foundations.AnalyticAlbanese
namespace HodgeLean.Foundations.Program

/-- A specified additive pointwise factor respects the algebraic group law. -/
theorem s4_selected_group_reflection
    (T : Type) [AddCommGroup T]
    (M A : Over (Spec ↧ℂ)) [GrpObj M] [GrpObj A]
    [IsCommMonObj M] [IsCommMonObj A]
    [IsIntegral M.left] [Smooth M.hom] [IsProjective M.hom]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (θ : T ≃ ComplexPoint M) (hθ0 : θ 0 = 1)
    (hθadd : ∀ z w, θ (z + w) = θ z * θ w)
    (H : T →+ Additive (ComplexPoint A)) (π : M ⟶ A)
    (he : ∀ z, Point.map π (θ z) = Additive.toMul (H z)) : IsMonHom π := by
  apply (faithful_group_reflection_aux M A).2
  · exact (congrArg (Point.map π) hθ0.symm).trans
      ((he 0).trans (congrArg Additive.toMul (map_zero H)))
  · intro x y
    obtain ⟨z, rfl⟩ := θ.surjective x
    obtain ⟨w, rfl⟩ := θ.surjective y
    exact (congrArg (Point.map π) (hθadd z w).symm).trans
      ((he (z + w)).trans ((congrArg Additive.toMul (H.map_add z w)).trans
        (congrArg₂ (fun a b : ComplexPoint A => a * b) (he z).symm (he w).symm)))

#print axioms s4_selected_group_reflection

end HodgeLean.Foundations.Program

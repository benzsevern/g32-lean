import HodgeLean.Foundations.Program.SchoenCartierUniversalGenericLift

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual Cartier universal property lifts every dominant field point dominantly through an integral base modification. -/
theorem s2_cartierUniversal_fieldLift (B' B : Over (Spec ↧ℂ))
    [IsIntegral B'.left] [IsIntegral B.left]
    (b : B' ⟶ B) (I : B.left.IdealSheafData) (hI : I.support ≠ ⊤)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B', u ≫ b = f)
    {K : Type} [Field K] (η : Spec (.of K) ⟶ B.left) [IsDominant η] :
    ∃ θ : Spec (.of K) ⟶ B'.left, θ ≫ b.left = η ∧ IsDominant θ := by
  obtain ⟨u, hu, hdom, _⟩ := s2_cartierUniversal_genericLift B' B b I hI huniv
  haveI := hdom
  let s := s2_dominantFieldFactor η
  haveI : IsDominant s := s2_fieldPointMap_dominant s
  refine ⟨s ≫ u, ?_, inferInstance⟩
  rw [Category.assoc, hu]
  exact s2_dominantFieldFactor_comp η

end HodgeLean.Foundations.Program

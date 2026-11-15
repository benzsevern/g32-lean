import HodgeLean.Foundations.Program.G32Native.ZeroPairComponent

/-! # Scheme instances on the retained component -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Transport the three native component instances along its specified isomorphism. -/
theorem g32n_componentInstances (k : ℕ) (Q : Over (Spec ↧ℂ))
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    IsIntegral Q.left ∧ Smooth Q.hom ∧ IsProjective Q.hom := by
  let PP : Over (Spec ↧ℂ) := Over.mk
    (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  haveI : IsIntegral PP.left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral k
  haveI : Smooth PP.hom :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_smooth k
  letI : IsProjective PP.hom := ⟨⟨⟨k, 𝟙 _, Category.id_comp _⟩⟩⟩
  have hi : IsIntegral Q.left := IsIntegral.of_isIso eQ.inv.left
  have hs : Smooth Q.hom := by
    rw [← Over.w eQ.hom]
    infer_instance
  have hp : IsProjective Q.hom := ⟨⟨⟨k, eQ.hom.left, Over.w eQ.hom⟩⟩⟩
  exact ⟨hi, hs, hp⟩

end HodgeLean.Foundations.Program

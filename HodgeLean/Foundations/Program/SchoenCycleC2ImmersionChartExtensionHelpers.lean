import HodgeLean.Foundations.Program.SchoenCycleC2SmoothImmersionChartsHelpers
import Mathlib.RingTheory.Extension.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program

/-- The actual section map of a complex closed immersion defines the
algebra extension on any ambient affine chart. -/
def s2e_closedImmersion_affine_extension
    (Q W : Over (Spec ↧ℂ)) (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (V : W.left.Opens) (hV : IsAffineOpen V) :
    letI := overSpecAlgebra Q (ι.left ⁻¹ᵁ V)
    Algebra.Extension.{0} ℂ Γ(Q.left, ι.left ⁻¹ᵁ V) := by
  letI := overSpecAlgebra W V
  letI := overSpecAlgebra Q (ι.left ⁻¹ᵁ V)
  have hmaps : W.hom.appLE ⊤ V le_top ≫ ι.left.app V =
      Q.hom.appLE ⊤ (ι.left ⁻¹ᵁ V) le_top := by
    have he : W.hom.appLE ⊤ V le_top ≫
        ι.left.appLE V (ι.left ⁻¹ᵁ V) le_rfl =
      Q.hom.appLE ⊤ (ι.left ⁻¹ᵁ V) le_top := by
      rw [Scheme.Hom.appLE_comp_appLE, Over.w ι]
    have happ : ι.left.appLE V (ι.left ⁻¹ᵁ V) le_rfl = ι.left.app V := by
      simp only [Scheme.Hom.appLE, homOfLE_refl, op_id]
      rw [Q.left.presheaf.map_id, Category.comp_id]
    rwa [happ] at he
  let φ : Γ(W.left, V) →ₐ[ℂ] Γ(Q.left, ι.left ⁻¹ᵁ V) :=
    { toRingHom := (ι.left.app V).hom
      commutes' := fun c => by
        exact congrArg (fun g : Γ(Spec ↧ℂ, ⊤) ⟶ Γ(Q.left, ι.left ⁻¹ᵁ V) =>
          g ((Scheme.ΓSpecIso ↧ℂ).inv c)) hmaps }
  exact Algebra.Extension.ofSurjective φ (ι.left.app_surjective V hV)

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenTowerCurveCoordinateAssembly
import HodgeLean.Foundations.Program.SchoenSchemeSectionAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Pullback on global sections remembers the specified coefficient algebra structure. -/
def s2t_overSectionsAlgHom {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) :
    Γ(Y.left, ⊤) →ₐ[ℂ] Γ(X.left, ⊤) := by
  refine { f.left.appTop.hom with commutes' := ?_ }
  intro c
  change f.left.appTop (Y.hom.appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso ↧ℂ).inv c)) =
    X.hom.appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso ↧ℂ).inv c)
  simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl, op_id,
    Functor.map_id, Category.comp_id]
  rw [Y.left.presheaf.map_id, X.left.presheaf.map_id]
  simp only [Category.comp_id]
  have he := congrArg (fun k : X.left ⟶ Spec ↧ℂ => k.appTop) (Over.w f)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using congrArg (fun k => k ((Scheme.ΓSpecIso ↧ℂ).inv c)) he

/-- The actual section action of automorphisms over the coefficient scheme commutes
with coefficient scalars. -/
theorem s2t_overSectionAction_smulCommClass (X : Over (Spec ↧ℂ))
    (G : Type) [Group G] (ρ : G →* Aut X) :
    let a := ((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ
    letI := s2_schemeSectionAction X.left G a
    SMulCommClass G ℂ Γ(X.left, ⊤) := by
  let a := ((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ
  letI := s2_schemeSectionAction X.left G a
  constructor
  intro g c b
  exact map_smul (s2t_overSectionsAlgHom (ρ g⁻¹).asIso.hom) c b

end HodgeLean.Foundations.Program

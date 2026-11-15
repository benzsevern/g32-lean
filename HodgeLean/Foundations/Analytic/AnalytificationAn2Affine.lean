import HodgeLean.Foundations.Analytic.AnalytificationDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

noncomputable section

set_option maxHeartbeats 400000

open Set Topology CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Foundations.Analytic

variable {X : Over (Spec ↧ℂ)} (U : X.left.affineOpens)

local instance AnalytificationAn2_openAlgebra : Algebra ℂ Γ(U.1.toScheme, ⊤) :=
  ((Scheme.ΓSpecIso ↧ℂ).inv ≫ (U.1.ι ≫ X.hom).appTop).hom.toAlgebra

theorem AnalytificationAn2_toSpecΓ_over :
    U.1.toScheme.toSpecΓ ≫
        ComplexPoint.affineSpecStructureMap Γ(U.1.toScheme, ⊤) =
      U.1.ι ≫ X.hom := by
  let φ : ↧ℂ ⟶ Γ(U.1.toScheme, ⊤) :=
    (Scheme.ΓSpecIso ↧ℂ).inv ≫ (U.1.ι ≫ X.hom).appTop
  apply ext_to_Spec
  exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ

def AnalytificationAn2_sectionIso :
    Γ(X.left, U.1) ≅ Γ(U.1.toScheme, ⊤) := U.1.topIso.symm

def AnalytificationAn2_affineSpecPointHomeomorph :
    ComplexPoint (ComplexPoint.openScheme X U.1) ≃ₜ
      ComplexPoint (Over.mk
        (ComplexPoint.affineSpecStructureMap Γ(U.1.toScheme, ⊤))) := by
  letI : IsAffine U.1.toScheme := U.2
  letI : IsIso U.1.toScheme.toSpecΓ := U.2.affine
  exact Point.isoMapHomeomorph
    (Over.isoMk (asIso U.1.toScheme.toSpecΓ) (AnalytificationAn2_toSpecΓ_over U))

theorem AnalytificationAn2_affineSpecPointHomeomorph_apply
    (z : ComplexPoint (ComplexPoint.openScheme X U.1)) :
    AnalytificationAn2_affineSpecPointHomeomorph U z =
      Point.map (Over.homMk U.1.toScheme.toSpecΓ (AnalytificationAn2_toSpecΓ_over U)) z := by
  rw [AnalytificationAn2_affineSpecPointHomeomorph]
  rfl

def AnalytificationAn2_pointAlgHomHomeomorph :
    ComplexPoint (ComplexPoint.openScheme X U.1) ≃ₜ
      (Γ(U.1.toScheme, ⊤) →ₐ[ℂ] ℂ) :=
  (AnalytificationAn2_affineSpecPointHomeomorph U).trans
    (ComplexPoint.affineSpecHomeomorph Γ(U.1.toScheme, ⊤))

theorem AnalytificationAn2_pointAlgHomHomeomorph_apply
    (z : ComplexPoint (ComplexPoint.openScheme X U.1))
    (s : Γ(U.1.toScheme, ⊤)) :
    AnalytificationAn2_pointAlgHomHomeomorph U z s = Point.evaluate ⊤ s z := by
  rw [AnalytificationAn2_pointAlgHomHomeomorph]
  rw [ComplexPoint.affineSpecHomeomorph, Homeomorph.trans_apply]
  change ComplexPoint.affineSpecEquiv Γ(U.1.toScheme, ⊤)
    ((AnalytificationAn2_affineSpecPointHomeomorph U) z) s = _
  rw [ComplexPoint.affineSpecEquiv_apply]
  rw [AnalytificationAn2_affineSpecPointHomeomorph_apply]
  rw [Point.evaluate_map]
  congr 2
  change U.1.toScheme.toSpecΓ.appTop
    ((Scheme.ΓSpecIso ↧Γ(U.1.toScheme, ⊤)).inv s) = s
  rw [Scheme.toSpecΓ_appTop]
  exact (Scheme.ΓSpecIso _).inv_hom_id_apply s

def AnalytificationAn2_openPointAlgHomHomeomorph :
    {z : ComplexPoint X // z ∈ Point.overOpen U.1} ≃ₜ
      (Γ(U.1.toScheme, ⊤) →ₐ[ℂ] ℂ) :=
  (ComplexPoint.openHomeomorph X U.1).symm.trans
    (AnalytificationAn2_pointAlgHomHomeomorph U)

theorem AnalytificationAn2_openPointAlgHomHomeomorph_apply
    (z : {z : ComplexPoint X // z ∈ Point.overOpen U.1})
    (s : Γ(X.left, U.1)) :
    AnalytificationAn2_openPointAlgHomHomeomorph U z
        ((AnalytificationAn2_sectionIso U).hom s) =
      Point.evaluate U.1 s z.1 := by
  rw [AnalytificationAn2_openPointAlgHomHomeomorph, Homeomorph.trans_apply,
    AnalytificationAn2_pointAlgHomHomeomorph_apply]
  let y := (ComplexPoint.openHomeomorph X U.1).symm z
  have h := ComplexPoint.evaluate_openEquiv X U.1
    ((AnalytificationAn2_sectionIso U).hom s) y
  have hy : Point.map (ComplexPoint.openInclusion X U.1) y = z.1 := by
    exact congrArg Subtype.val ((ComplexPoint.openHomeomorph X U.1).apply_symm_apply z)
  calc
    Point.evaluate ⊤ ((AnalytificationAn2_sectionIso U).hom s) y =
        Point.evaluate (U.1.ι ''ᵁ ⊤)
          ((U.1.ι.appIso ⊤).inv ((AnalytificationAn2_sectionIso U).hom s))
          (Point.map (ComplexPoint.openInclusion X U.1) y) := h.symm
    _ = Point.evaluate U.1 s (Point.map (ComplexPoint.openInclusion X U.1) y) := by
      rw [ComplexPoint.evaluate_eq U.1.ι_image_top]
      congr 2
      rw [Scheme.Opens.ι_appIso]
      simp only [Iso.refl_inv]
      change (U.1.topIso).hom ((U.1.topIso).inv s) = s
      exact U.1.topIso.inv_hom_id_apply s
    _ = Point.evaluate U.1 s z.1 := by rw [hy]

end HodgeLean.Foundations.Analytic

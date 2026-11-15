import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealSection
import HodgeLean.Foundations.Program.G32Native.AffineIdealSectionInclusion
import HodgeLean.Foundations.Curves.Picard.LineBundles.PullbackScalars

/-! # Original equation functions in canonical affine ideal sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual affine ideal inclusion of a transported original local
section is exactly its original regular function on the ambient open. -/
theorem affineOpenIdealSection_function {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    (U : W.left.Opens) (hU : IsAffineOpen U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) :
    affineIdealSectionInclusion Γ(W.left, U) ((i.left ∣_ U) ≫ hU.isoSpec.hom)
      (show (moduleSpecΓFunctor (R := Γ(W.left, U))).obj _ from
        (affineOpenIdealSection i.left U hU s).val.app (op ⊤)
          (1 : Γ(Spec Γ(W.left, U), ⊤))) = conormalLocalFunction i U s := by
  let R := Γ(W.left, U)
  let j := (i.left ∣_ U) ≫ hU.isoSpec.hom
  let t := affineOpenIdealSection i.left U hU s
  let a := s ≫ (Scheme.Modules.pullback U.ι).map (conormalIdealInclusion i.left) ≫
    (pullbackUnit U.ι).hom
  change (Scheme.ΓSpecIso R).hom
    (s2e_idealModule_sections_equiv j ⊤ (t.val.app (op ⊤) (1 : Γ(Spec R, ⊤)))).val = _
  rw [s2e_idealModule_sections_equiv_coe]
  change (Scheme.ΓSpecIso R).hom
    ((t ≫ conormalIdealInclusion j).val.app (op ⊤) (1 : Γ(Spec R, ⊤))) = _
  rw [affineOpenIdealSection_inclusion]
  have hc := pullbackUnitEnd_coefficient hU.isoSpec.inv a ⊤
  change ((pullbackUnit hU.isoSpec.inv).inv ≫ (Scheme.Modules.pullback hU.isoSpec.inv).map a ≫
    (pullbackUnit hU.isoSpec.inv).hom).val.app (op ⊤) (1 : Γ(Spec R, ⊤)) =
      hU.isoSpec.inv.appTop (a.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤))) at hc
  rw [hc, IsAffineOpen.isoSpec_inv_appTop, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

#print axioms affineOpenIdealSection_function
end HodgeLean.Foundations.Program.G32Native

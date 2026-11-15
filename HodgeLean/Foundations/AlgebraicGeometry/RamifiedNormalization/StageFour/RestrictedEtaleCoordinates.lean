import HodgeLean.Foundations.Program.SchoenTowerL1aEtaleRestriction

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual structure-map etale coordinates restrict to the same smaller affine neighborhood as the original branch equation. -/
theorem etale_coordinate_map_restrict
    (Z : Over (Spec ↧ℂ)) (U V : Z.left.affineOpens) (hUV : U.1 ≤ V.1)
    {ι : Type} (z : ι → Γ(Z.left, V))
    (hz : (MvPolynomial.eval₂Hom ((Z.hom.appLE ⊤ V.1 le_top).hom) z).Etale) :
    (MvPolynomial.eval₂Hom ((Z.hom.appLE ⊤ U.1 le_top).hom)
      (fun j => (Z.left.presheaf.map (homOfLE hUV).op).hom (z j))).Etale := by
  let res := (Z.left.presheaf.map (homOfLE hUV).op).hom
  have hcoeff : res.comp (Z.hom.appLE ⊤ V.1 le_top).hom =
      (Z.hom.appLE ⊤ U.1 le_top).hom := by
    change (Z.hom.appLE ⊤ V.1 le_top ≫ Z.left.presheaf.map (homOfLE hUV).op).hom = _
    rw [Scheme.Hom.appLE_map]
  have hmap : MvPolynomial.eval₂Hom ((Z.hom.appLE ⊤ U.1 le_top).hom) (fun j => res (z j)) =
      res.comp (MvPolynomial.eval₂Hom ((Z.hom.appLE ⊤ V.1 le_top).hom) z) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact (congrArg (fun f => f a) hcoeff).symm
    · intro j
      rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
  change (MvPolynomial.eval₂Hom ((Z.hom.appLE ⊤ U.1 le_top).hom) (fun j => res (z j))).Etale
  rw [hmap]
  exact RingHom.Etale.stableUnderComposition _ _ hz
    (s2v_l1a_affine_section_restriction_etale V U hUV)

end AlgebraicGeometry.RamifiedNormalization.StageFour

import HodgeLean.Foundations.Program.G32Native.PairedC3IntersectionQuotientSquare
import HodgeLean.Foundations.Program.G32Native.PairedC3IntersectionProjectiveFibre
import HodgeLean.Foundations.Program.G32Native.PairedC3SpecRestrictionAlgebra

/-! # The marked square on the original intersection pullback -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- A normalized ideal calculation on the quotient chart supplies the marked
square on the canonical pullback of the original intersection inclusion. -/
theorem pairedC3_canonical_intersection_fibre
    (X : Over (Spec ↧ℂ)) (N I : X.left.IdealSheafData) (V : X.left.affineOpens)
    (i : Fin 2) :
    let pI := I.subschemeCover.f V ≫ I.subschemeι ≫ X.hom
    letI := pairedC3SpecAlgebra pI
    ∀ z : Γ(X.left, V) ⧸ I.ideal V,
      (N.ideal V).map (Ideal.Quotient.mk (I.ideal V)) = Ideal.span {z - 1} →
      let b := Scheme.IdealSheafData.inclusion (show I ≤ N ⊔ I from le_sup_right)
      IsPullback (pullback.snd b (I.subschemeCover.f V))
        (pullback.fst b (I.subschemeCover.f V) ≫ (N ⊔ I).subschemeι ≫ X.hom)
        (projectiveLineChart i z).left (projectiveLineChart i (1 : ℂ)).left := by
  dsimp only
  let pI := I.subschemeCover.f V ≫ I.subschemeι ≫ X.hom
  letI := pairedC3SpecAlgebra pI
  intro z hN
  let b := Scheme.IdealSheafData.inclusion (show I ≤ N ⊔ I from le_sup_right)
  let q := Ideal.Quotient.factor (show I.ideal V ≤ N.ideal V ⊔ I.ideal V from le_sup_right)
  have hs := pairedC3_subscheme_inclusion_quotient_square I (N ⊔ I) le_sup_right V
  have hp := pairedC3_intersection_projective_fibre Γ(X.left, V)
    (N.ideal V) (I.ideal V) i z hN
  let e := hs.flip.isoPullback
  have he₁ : e.hom ≫ pullback.fst b (I.subschemeCover.f V) =
      (N ⊔ I).subschemeCover.f V := hs.flip.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd b (I.subschemeCover.f V) =
      Spec.map (CommRingCat.ofHom q) := hs.flip.isoPullback_hom_snd
  have ht : Spec.map (CommRingCat.ofHom (q.comp (algebraMap ℂ _))) =
      e.hom ≫ pullback.fst b (I.subschemeCover.f V) ≫ (N ⊔ I).subschemeι ≫ X.hom := by
    change Spec.map (CommRingCat.ofHom (algebraMap ℂ _) ≫ CommRingCat.ofHom q) = _
    rw [Spec.map_comp]
    change Spec.map (CommRingCat.ofHom q) ≫ ComplexPoint.affineSpecStructureMap _ = _
    rw [pairedC3_spec_algebra_structure_map pI]
    rw [← Category.assoc e.hom, he₁]
    have h := congrArg (fun f => f ≫ I.subschemeι ≫ X.hom) hs.w
    simpa only [pI, q, Category.assoc,
      Scheme.IdealSheafData.inclusion_subschemeι_assoc] using h
  exact (hp.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using ht)
    (by simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using he₂.symm)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])).flip

#print axioms pairedC3_canonical_intersection_fibre
end HodgeLean.Foundations.Program.G32Native

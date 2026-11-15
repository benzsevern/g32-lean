import HodgeLean.Foundations.QuotientDuality.ProperCycleClosedSupportChainSections

/-! # Actual extension of original supported chain section complexes
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An additive section functor commutes with extension of an actual chain complex by zero; this comparison retains the original objects and differentials in every retained degree.
Source: HomologicalComplex.extend; HomologicalComplex.Hom.isoOfComponents; CategoryTheory.Functor.map_isZero.
HC no distance; AV milestone no distance. -/
def properCycle_section_functor_extend_iso
    {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : ChainComplex C ℕ) :
    (((F.mapHomologicalComplex (.down ℕ)).obj K).extend ComplexShape.embeddingDownNat) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingDownNat) := by
  let e (a : Option ℕ) :
      extend.X ((F.mapHomologicalComplex (.down ℕ)).obj K) a ≅ F.obj (extend.X K a) :=
    match a with
    | some _ => Iso.refl _
    | none => (isZero_zero D).iso (F.map_isZero (isZero_zero C))
  exact HomologicalComplex.Hom.isoOfComponents
    (fun i => e (ComplexShape.embeddingDownNat.r i)) (by
      intro i j hij
      change (e _).hom ≫ F.map (extend.d K _ _) =
        extend.d ((F.mapHomologicalComplex (.down ℕ)).obj K) _ _ ≫ (e _).hom
      cases ComplexShape.embeddingDownNat.r i <;>
        cases ComplexShape.embeddingDownNat.r j <;>
        simp [e, extend.d])

end HodgeLean.Foundations.QuotientDuality

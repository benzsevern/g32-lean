import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program

/-- An actual dominant field point factors through the spectrum of the function field of its integral target. -/
def s2_dominantFieldFactor {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
    (η : Spec (.of K) ⟶ X) [IsDominant η] : Spec (.of K) ⟶ Spec X.functionField :=
  let h : η (closedPoint K) = genericPoint X := by
    rw [Subsingleton.elim (closedPoint K) (genericPoint (Spec (.of K)))]
    exact s2_dominant_genericPoint η
  Spec.map (X.presheaf.stalkSpecializes (specializes_of_eq h) ≫
    η.stalkMap (closedPoint K) ≫ (stalkClosedPointIso (.of K)).hom)

/-- The actual field factor recovers the specified dominant point morphism. -/
theorem s2_dominantFieldFactor_comp {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
    (η : Spec (.of K) ⟶ X) [IsDominant η] :
    s2_dominantFieldFactor η ≫ X.fromSpecStalk (genericPoint X) = η := by
  dsimp only [s2_dominantFieldFactor]
  simp only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  rw [← Spec_stalkClosedPointIso, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

/-- Every actual morphism between spectra of fields is dominant. -/
theorem s2_fieldPointMap_dominant {K L : Type} [Field K] [Field L]
    (f : Spec (.of K) ⟶ Spec (.of L)) : IsDominant f := by
  haveI : Surjective f := ⟨fun x => ⟨closedPoint K, Subsingleton.elim _ x⟩⟩
  infer_instance

end HodgeLean.Foundations.Program

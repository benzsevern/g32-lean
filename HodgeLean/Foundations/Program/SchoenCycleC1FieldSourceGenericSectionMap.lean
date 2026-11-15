import HodgeLean.Foundations.Program.SchoenCycleC1FieldSourceGenericEmbedding

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A retained generic field factorization identifies the rational section
embedding with the canonical original-field section map of the actual source. -/
theorem s2e_c1_field_source_generic_section_map
    (L : Type) [Field L] (X : Scheme) [IsIntegral X]
    (η : Spec (CommRingCat.of L) ⟶ X) (φ : X.functionField →+* L)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X) = η) :
    letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
    φ.comp (X.germToFunctionField ⊤).hom =
      (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp η.appTop.hom := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  have he : η.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom =
      X.germToFunctionField ⊤ ≫ CommRingCat.ofHom φ := by
    rw [← hφ, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
      Scheme.fromSpecStalk_appTop]
    simp only [Category.assoc, Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]
    simp
    erw [Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom he.symm

end HodgeLean.Foundations.Program

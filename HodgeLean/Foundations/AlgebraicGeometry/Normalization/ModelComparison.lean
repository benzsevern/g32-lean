import HodgeLean.Foundations.AlgebraicGeometry.Normalization.ModelComparisonProofs

/-! General APIs as implications from the displayed geometric and coefficient inputs.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Normalization

/-- General library interface.
Source: Stacks Project, Section 29.54 (Normalization); existing s2e_c1_normalization_iso_of_normal_model. -/
theorem modelComparison
    {T X B : Scheme.{0}} [IsIntegral T] [IsIntegral X]
    (f : T ⟶ B) [QuasiCompact f] [QuasiSeparated f]
    (j : T ⟶ X) [IsDominant j] (π : X ⟶ B) [IsIntegralHom π]
    (h : f = j ≫ π) (hnormal : zmtiso_IsNormal X)
    (hgeneric : zmtiso_IsBirational j) :
    ∃ E : f.normalization ≅ X,
      f.toNormalization ≫ E.hom = j ∧ E.hom ≫ π = f.fromNormalization :=
  modelComparison_aux f j π h hnormal hgeneric


/-- General library interface.
Source: Stacks Project, Section 29.54 (Normalization); existing s2e_c1_normalization_etale_of_normal_model. -/
theorem etale_of_model
    {T X B : Scheme.{0}} [IsIntegral T] [IsIntegral X]
    (f : T ⟶ B) [QuasiCompact f] [QuasiSeparated f]
    (j : T ⟶ X) [IsDominant j] (π : X ⟶ B) [IsIntegralHom π] [Etale π]
    (h : f = j ≫ π) (hnormal : zmtiso_IsNormal X)
    (hgeneric : zmtiso_IsBirational j) : Etale f.fromNormalization :=
  etale_of_model_aux f j π h hnormal hgeneric


-- The identity model supplies the specified source map and base square.
example (X : Scheme.{0}) :
    ∃ E : (𝟙 X : X ⟶ X).normalization ≅ X,
      (𝟙 X : X ⟶ X).toNormalization ≫ E.hom = 𝟙 X ∧
        E.hom ≫ 𝟙 X = (𝟙 X : X ⟶ X).fromNormalization := by
  refine ⟨(asIso (𝟙 X : X ⟶ X).toNormalization).symm, ?_, ?_⟩
  · exact IsIso.hom_inv_id _
  · apply (cancel_epi (𝟙 X : X ⟶ X).toNormalization).mp
    change ((𝟙 X : X ⟶ X).toNormalization ≫ inv (𝟙 X : X ⟶ X).toNormalization) ≫ 𝟙 X = _
    rw [IsIso.hom_inv_id, Category.id_comp,
      Scheme.Hom.toNormalization_fromNormalization]

-- An integral etale map has an etale relative-normalization projection.
example {X B : Scheme.{0}} (f : X ⟶ B) [IsIntegralHom f] [Etale f] :
    Etale f.fromNormalization := by
  have h : f.fromNormalization = inv f.toNormalization ≫ f := by
    apply (cancel_epi f.toNormalization).mp
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp,
      Scheme.Hom.toNormalization_fromNormalization]
  rw [h]
  infer_instance

end AlgebraicGeometry.Normalization

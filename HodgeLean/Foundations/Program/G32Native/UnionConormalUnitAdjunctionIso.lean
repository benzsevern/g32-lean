import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.EpiMono

/-! # Pullback unit epimorphy under an adjunction identification -/
noncomputable section
open CategoryTheory
namespace HodgeLean.Foundations.Program.G32Native

/-- A natural isomorphism between right adjoints transports epimorphy of their units. -/
lemma unionConormal_unit_epi_of_rightAdjointIso
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) (M : C)
    [Epi (adj₁.unit.app M)] : Epi (adj₂.unit.app M) := by
  let a := (conjugateIsoEquiv adj₁ adj₂).symm e
  have ha : (conjugateEquiv adj₁ adj₂).symm e.hom = a.hom := rfl
  have he := unit_conjugateEquiv_symm adj₁ adj₂ e.hom M
  rw [ha] at he
  haveI : Epi (adj₂.unit.app M ≫ R₂.map (a.hom.app M)) := by
    rw [← he]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (R₂.map (a.hom.app M))).mp inferInstance

end HodgeLean.Foundations.Program.G32Native

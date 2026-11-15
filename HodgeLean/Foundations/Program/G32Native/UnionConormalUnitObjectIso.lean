import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.EpiMono

/-! # Pullback unit epimorphy under an object identification -/
noncomputable section
open CategoryTheory
namespace HodgeLean.Foundations.Program.G32Native

/-- An object isomorphism transports epimorphy of an adjunction unit. -/
lemma unionConormal_unit_epi_of_iso
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {M N : C} (e : M ≅ N) [Epi (adj.unit.app N)] :
    Epi (adj.unit.app M) := by
  have he : adj.unit.app M ≫ (L ⋙ R).map e.hom = e.hom ≫ adj.unit.app N :=
    (adj.unit.naturality e.hom).symm
  haveI : Epi (adj.unit.app M ≫ (L ⋙ R).map e.hom) := by
    rw [he]
    infer_instance
  exact (epi_comp_iff_of_isIso _ ((L ⋙ R).map e.hom)).mp inferInstance

end HodgeLean.Foundations.Program.G32Native

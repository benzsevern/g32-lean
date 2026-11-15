import HodgeLean.Foundations.Program.G32Native.UnionConormalLocalExact

/-! # Epimorphy through natural functor identifications -/
noncomputable section
open CategoryTheory
namespace HodgeLean.Foundations.Program.G32Native

/-- A natural functor isomorphism transports epimorphy of an image map. -/
lemma unionConormal_epi_map_of_natIso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {M N : C} (f : M ⟶ N) [Epi (F.map f)] : Epi (G.map f) := by
  have he : G.map f = e.inv.app M ≫ F.map f ≫ e.hom.app N := by
    rw [e.hom.naturality f, Iso.inv_hom_id_app_assoc]
  rw [he]
  infer_instance

end HodgeLean.Foundations.Program.G32Native

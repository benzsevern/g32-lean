import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Transporting a short exact sequence through identifications of its terms -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program.G32Native

/-- Termwise identifications transport the existence of a short exact sequence. -/
lemma unionConormal_shortExact_of_termIsos
    {C : Type*} [Category C] [HasZeroMorphisms C]
    (S : ShortComplex C) (hS : S.ShortExact) {A B D : C}
    (e₁ : A ≅ S.X₁) (e₂ : B ≅ S.X₂) (e₃ : D ≅ S.X₃) :
    ∃ (f : A ⟶ B) (g : B ⟶ D) (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact := by
  let f := e₁.hom ≫ S.f ≫ e₂.inv
  let g := e₂.hom ≫ S.g ≫ e₃.inv
  have hfg : f ≫ g = 0 := by
    dsimp only [f, g]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc S.f S.g, S.zero, zero_comp, comp_zero]
  let T := ShortComplex.mk f g hfg
  let e : T ≅ S := ShortComplex.isoMk e₁ e₂ e₃
    (by dsimp [T, f]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by dsimp [T, g]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  exact ⟨f, g, hfg, ShortComplex.shortExact_of_iso e.symm hS⟩

/-- Transporting a map through two term isomorphisms commutes with any functor. -/
lemma unionConormal_map_termIsos
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B P Q : C} {X : D} (c : X ⟶ F.obj A) (e₁ : A ≅ P) (e₂ : B ≅ Q)
    (u : A ⟶ B) (v : P ⟶ Q) (hu : u = e₁.hom ≫ v ≫ e₂.inv) :
    (c ≫ F.map u) ≫ F.map e₂.hom = (c ≫ F.map e₁.hom) ≫ F.map v := by
  rw [hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp e₂.inv e₂.hom, Iso.inv_hom_id, F.map_id, Category.comp_id]

/-- A transported map and a naturality square give the transported composite. -/
lemma unionConormal_transport_naturality
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B P Q : C} {X Y Z : D} (c : X ⟶ F.obj A)
    (e₁ : A ≅ P) (e₂ : B ≅ Q) (u : A ⟶ B) (v : P ⟶ Q)
    (hu : u = e₁.hom ≫ v ≫ e₂.inv)
    (a : F.obj P ⟶ Y) (b : F.obj Q ⟶ Z) (w : Y ⟶ Z)
    (hn : F.map v ≫ b = a ≫ w) :
    (c ≫ F.map u) ≫ (F.map e₂.hom ≫ b) =
      ((c ≫ F.map e₁.hom) ≫ a) ≫ w := by
  rw [← Category.assoc, unionConormal_map_termIsos F c e₁ e₂ u v hu]
  simpa only [Category.assoc] using congrArg (fun t => (c ≫ F.map e₁.hom) ≫ t) hn

/-- The map of a functorially transported composite isomorphism is explicit. -/
lemma unionConormal_mapIso_trans_hom
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {Z : D} (e : X ≅ Y) (a : F.obj Y ≅ Z) :
    (F.mapIso e ≪≫ a).hom = F.map e.hom ≫ a.hom := rfl

/-- A presentation square remains a square after changing the module coordinates. -/
lemma unionConormal_transport_map_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B P Q : C} {X Y : D} (c : X ⟶ Y)
    (eA : X ≅ F.obj A) (eB : Y ≅ F.obj B) (e₁ : A ≅ P) (e₂ : B ≅ Q)
    (u : A ⟶ B) (v : P ⟶ Q)
    (h : c ≫ eB.hom = eA.hom ≫ F.map u)
    (hn : u ≫ e₂.hom = e₁.hom ≫ v) :
    c ≫ (eB ≪≫ F.mapIso e₂).hom =
      (eA ≪≫ F.mapIso e₁).hom ≫ F.map v := by
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [hn]

end HodgeLean.Foundations.Program.G32Native

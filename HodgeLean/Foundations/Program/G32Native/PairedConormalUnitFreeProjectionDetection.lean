import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeProjectionDetection

/-! # Exact component detection in the actual unit-plus-free presentation target -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- Additive transport detects the actual presentation column by its distinguished
unit coordinate and its specified finite free coordinates. -/
theorem conormal_map_unit_free_projections_detect_zero
    (T : Scheme.{0}) (k : ℕ) {C : Type*} [Category* C] [Preadditive C]
    (F : T.Modules ⥤ C) [F.Additive] {B : C}
    (u : B ⟶ F.obj (SheafOfModules.unit T.ringCatSheaf ⊞
      SheafOfModules.free (R := T.ringCatSheaf) (Fin k)))
    (h0 : u ≫ F.map (biprod.fst : SheafOfModules.unit T.ringCatSheaf ⊞
      SheafOfModules.free (R := T.ringCatSheaf) (Fin k) ⟶ _) = 0)
    (hi : ∀ i : Fin k, u ≫ F.map ((biprod.snd :
      SheafOfModules.unit T.ringCatSheaf ⊞
        SheafOfModules.free (R := T.ringCatSheaf) (Fin k) ⟶ _) ≫
          i1_freeSheafProjection T k i) = 0) : u = 0 := by
  let A := SheafOfModules.unit T.ringCatSheaf
  let E := SheafOfModules.free (R := T.ringCatSheaf) (Fin k)
  have hs : u ≫ F.map (biprod.snd : A ⊞ E ⟶ E) = 0 := by
    apply conormal_map_free_projections_detect_zero T k F
    intro i
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
    exact hi i
  have ht : (biprod.fst : A ⊞ E ⟶ A) ≫ biprod.inl +
      (biprod.snd : A ⊞ E ⟶ E) ≫ biprod.inr = 𝟙 (A ⊞ E) := biprod.total
  calc
    u = u ≫ F.map (𝟙 _) := by rw [CategoryTheory.Functor.map_id, Category.comp_id]
    _ = 0 := by
      rw [← ht, CategoryTheory.Functor.map_add, Preadditive.comp_add, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp, ← Category.assoc, h0, zero_comp,
        ← Category.assoc, hs, zero_comp, add_zero]

end HodgeLean.Foundations.Program.G32Native

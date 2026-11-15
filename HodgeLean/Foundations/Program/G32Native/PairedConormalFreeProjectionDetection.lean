import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeProjectionResolution
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Detect actual pulled free-module arrows by the specified projections -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- Any additive transport retains zero detection by the actual finite free coordinate projections. -/
theorem conormal_map_free_projections_detect_zero
    (T : Scheme.{0}) (k : ℕ) {C : Type*} [Category* C] [Preadditive C]
    (F : T.Modules ⥤ C) [F.Additive] {B : C}
    (u : B ⟶ F.obj (SheafOfModules.free (R := T.ringCatSheaf) (Fin k)))
    (hu : ∀ i : Fin k, u ≫ F.map (i1_freeSheafProjection T k i) = 0) : u = 0 := by
  calc
    u = u ≫ F.map (𝟙 _) := by rw [CategoryTheory.Functor.map_id, Category.comp_id]
    _ = 0 := by
      rw [← conormal_free_projection_resolution T k, CategoryTheory.Functor.map_sum, Preadditive.comp_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [CategoryTheory.Functor.map_comp, ← Category.assoc, hu i, zero_comp]

end HodgeLean.Foundations.Program.G32Native

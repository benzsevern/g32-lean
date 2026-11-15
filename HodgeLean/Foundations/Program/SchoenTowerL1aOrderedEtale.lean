import HodgeLean.Foundations.Program.SchoenCycleGeometryDefs

/-! # Etale maps on ordered powers

Implication from an etale curve map to an etale map on the retained iterated
ordered powers. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped MonoidalCategory
namespace HodgeLean.Foundations.Program

/-- The retained product lift commutes with precomposition.
Source: Mac Lane, Categories for the Working Mathematician, III.4, products. -/
theorem s2v_l1a_lift_precompose
    {T T' Z : Over (Spec ↧ℂ)} (a : T ⟶ T')
    (h : ℕ) (f : Fin h → (T' ⟶ Z)) :
    a ≫ s2_lift h f = s2_lift h (fun j => a ≫ f j) := by
  induction h with
  | zero => exact CartesianMonoidalCategory.toUnit_unique _ _
  | succ h ih =>
      change a ≫ CartesianMonoidalCategory.lift _ _ =
        CartesianMonoidalCategory.lift _ _
      rw [CartesianMonoidalCategory.comp_lift, ih]

/-- The retained power map at a successor is the binary product of the curve map and its preceding power.
Source: Mac Lane, Categories for the Working Mathematician, III.4, products. -/
theorem s2v_l1a_powerMap_succ
    {Y Z : Over (Spec ↧ℂ)} (p : Y ⟶ Z) (h : ℕ) :
    s2_powerMap p (h + 1) = p ⊗ₘ s2_powerMap p h := by
  change CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.fst Y (g3_power Y h) ≫ p)
    (s2_lift h (fun j =>
      (CartesianMonoidalCategory.snd Y (g3_power Y h) ≫ g3_proj Y h j) ≫ p)) =
    p ⊗ₘ s2_powerMap p h
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.tensorHom_fst]
  · rw [CartesianMonoidalCategory.lift_snd, CartesianMonoidalCategory.tensorHom_snd]
    rw [s2_powerMap, s2v_l1a_lift_precompose]
    congr 1

/-- Etaleness of a curve map is preserved on every retained ordered power.
Source: Hartshorne, Algebraic Geometry, III.10, base change and composition of etale maps. -/
theorem s2v_l1a_ordered_power_etale
    {Y Z : Over (Spec ↧ℂ)} (p : Y ⟶ Z) [Etale p.left] (h : ℕ) :
    Etale (s2_powerMap p h).left := by
  induction h with
  | zero =>
      have heq : s2_powerMap p 0 = 𝟙 (g3_power Z 0) :=
        CartesianMonoidalCategory.toUnit_unique _ _
      rw [heq]
      change Etale (𝟙 (Spec ↧ℂ))
      infer_instance
  | succ h ih =>
      rw [s2v_l1a_powerMap_succ, Over.tensorHom_left]
      let : MorphismProperty.IsStableUnderComposition (@Etale.{0}) :=
        { comp_mem := fun f g hf hg => by
            let := hf
            let := hg
            infer_instance }
      let : MorphismProperty.IsStableUnderBaseChange (@Etale.{0}) :=
        Etale.etale_isStableUnderBaseChange
      exact MorphismProperty.pullbackMap (P := @Etale.{0})
        (inferInstance : Etale p.left) ih (Over.w p).symm (Over.w (s2_powerMap p h)).symm

end HodgeLean.Foundations.Program

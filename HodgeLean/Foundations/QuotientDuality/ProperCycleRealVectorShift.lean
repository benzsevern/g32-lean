import HodgeLean.Foundations.QuotientDuality.ProperCycleRealShift
import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTransport
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Local homology shifts for actual finite real vector factors -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Split the first actual real coordinate from a finite tuple.
Source: Munkres, Topology, section 19, finite product topology.
HC no distance; AV milestone no distance. -/
def properCycle_real_fin_succ_homeomorph (r : ℕ) :
    (Fin (r + 1) → ℝ) ≃ₜ (ℝ × (Fin r → ℝ)) where
  toEquiv := (Fin.consEquiv (fun _ : Fin (r + 1) => ℝ)).symm
  continuous_toFun := (continuous_apply 0).prodMk
    (continuous_pi (fun i : Fin r => continuous_apply i.succ))
  continuous_invFun := by
    apply continuous_pi
    intro i
    cases i using Fin.cases with
    | zero => exact continuous_fst
    | succ i => exact (continuous_apply i).comp continuous_snd

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual local homology of a finite real product shifts by the number of tangential coordinates.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer–Vietoris.
HC no distance; AV milestone no distance. -/
def properCycle_real_pi_local_homology_iso
    (r : ℕ) (Y : TopCat.{0}) [T1Space Y] (y : Y) (n : ℕ) :
    orientationGroup (TopCat.of ((Fin r → ℝ) × Y)) (n + r) (0, y) ≅
      orientationGroup Y n y := by
  induction r with
  | zero =>
      let e : ((Fin 0 → ℝ) × Y) ≃ₜ Y :=
        { toFun := Prod.snd
          invFun := fun y => (0, y)
          left_inv := fun z => Prod.ext (Subsingleton.elim _ _) rfl
          right_inv := fun _ => rfl
          continuous_toFun := continuous_snd
          continuous_invFun := continuous_const.prodMk continuous_id }
      exact properCycle_local_homology_homeomorph_iso
        (X := TopCat.of ((Fin 0 → ℝ) × Y)) (Y := Y) e (0, y) n
  | succ r ih =>
      let e : ((Fin (r + 1) → ℝ) × Y) ≃ₜ (ℝ × ((Fin r → ℝ) × Y)) :=
        ((properCycle_real_fin_succ_homeomorph r).prodCongr (Homeomorph.refl Y)).trans
          (Homeomorph.prodAssoc ℝ (Fin r → ℝ) Y)
      have he : e (0, y) = (0, (0, y)) := rfl
      let E := properCycle_local_homology_homeomorph_iso
        (X := TopCat.of ((Fin (r + 1) → ℝ) × Y))
        (Y := TopCat.of (ℝ × ((Fin r → ℝ) × Y))) e (0, y) ((n + r) + 1)
      rw [he] at E
      exact E ≪≫ properCycle_real_product_local_homology_iso
        (TopCat.of ((Fin r → ℝ) × Y)) (0, y) (n + r) ≪≫ ih

/-- A basis gives actual continuous vector coordinates and preserves the normal coordinate literally.
Source: Axler, Linear Algebra Done Right, third edition, chapter 2, coordinates in finite-dimensional spaces.
HC no distance; AV milestone no distance. -/
def properCycle_vector_product_coordinates
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) : (E × Y) ≃ₜ ((Fin (Module.finrank ℝ E) → ℝ) × Y) :=
  (ContinuousLinearEquiv.ofFinrankEq
    (by simp only [Module.finrank_pi, Fintype.card_fin]) :
      E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)).toHomeomorph.prodCongr (Homeomorph.refl Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Any actual finite real normed tangential factor shifts normal local homology by its real dimension.
Source: Hatcher, Algebraic Topology, section 2.2; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
def properCycle_vector_product_local_homology_iso
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] (y : Y) (n : ℕ) :
    orientationGroup (TopCat.of (E × Y)) (n + Module.finrank ℝ E) (0, y) ≅
      orientationGroup Y n y := by
  let e := properCycle_vector_product_coordinates E Y
  have he : e (0, y) = (0, y) := by
    apply Prod.ext
    · exact (ContinuousLinearEquiv.ofFinrankEq
        (by simp only [Module.finrank_pi, Fintype.card_fin]) :
          E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)).map_zero
    · rfl
  let H := properCycle_local_homology_homeomorph_iso
    (X := TopCat.of (E × Y)) (Y := TopCat.of ((Fin (Module.finrank ℝ E) → ℝ) × Y))
    e (0, y) (n + Module.finrank ℝ E)
  rw [he] at H
  exact H ≪≫ properCycle_real_pi_local_homology_iso (Module.finrank ℝ E) Y y n

end HodgeLean.Foundations.QuotientDuality

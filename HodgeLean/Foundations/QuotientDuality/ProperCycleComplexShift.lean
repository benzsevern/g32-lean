import HodgeLean.Foundations.QuotientDuality.ProperCycleRealShift
import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTransport

/-! # Local normal homology shifts for complex tangential coordinates -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular Topology
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Two real tangential shifts give the local homology shift of one actual complex coordinate.
Source: Hatcher, Algebraic Topology, section 2.2; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
def properCycle_complex_product_local_homology_iso
    (Y : TopCat.{0}) [T1Space Y] (y : Y) (n : ℕ) :
    orientationGroup (TopCat.of (ℂ × Y)) (n + 2) (0, y) ≅
      orientationGroup Y n y := by
  let e : (ℂ × Y) ≃ₜ (ℝ × (ℝ × Y)) :=
    (Complex.equivRealProdCLM.toHomeomorph.prodCongr (Homeomorph.refl Y)).trans
      (Homeomorph.prodAssoc ℝ ℝ Y)
  have he : e (0, y) = (0, (0, y)) := rfl
  let E := properCycle_local_homology_homeomorph_iso
    (X := TopCat.of (ℂ × Y)) (Y := TopCat.of (ℝ × (ℝ × Y))) e (0, y) (n + 2)
  rw [he] at E
  exact E ≪≫ properCycle_real_product_local_homology_iso (TopCat.of (ℝ × Y)) (0, y) (n + 1) ≪≫
    properCycle_real_product_local_homology_iso Y y n

/-- Split the first actual complex coordinate from a finite tuple, with its product topology.
Source: Munkres, Topology, section 19, finite product topology.
HC no distance; AV milestone no distance. -/
def properCycle_complex_fin_succ_homeomorph (r : ℕ) :
    (Fin (r + 1) → ℂ) ≃ₜ (ℂ × (Fin r → ℂ)) where
  toEquiv := (Fin.consEquiv (fun _ : Fin (r + 1) => ℂ)).symm
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
/-- Actual finite complex tangential coordinates shift local normal homology by twice their number.
Source: Hatcher, Algebraic Topology, section 2.2; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
def properCycle_complex_pi_local_homology_iso
    (r : ℕ) (Y : TopCat.{0}) [T1Space Y] (y : Y) (n : ℕ) :
    orientationGroup (TopCat.of ((Fin r → ℂ) × Y)) (n + 2 * r) (0, y) ≅
      orientationGroup Y n y := by
  induction r with
  | zero =>
      let e : ((Fin 0 → ℂ) × Y) ≃ₜ Y :=
        { toFun := Prod.snd
          invFun := fun y => (0, y)
          left_inv := fun z => Prod.ext (Subsingleton.elim _ _) rfl
          right_inv := fun _ => rfl
          continuous_toFun := continuous_snd
          continuous_invFun := continuous_const.prodMk continuous_id }
      exact properCycle_local_homology_homeomorph_iso
        (X := TopCat.of ((Fin 0 → ℂ) × Y)) (Y := Y) e (0, y) n
  | succ r ih =>
      let e : ((Fin (r + 1) → ℂ) × Y) ≃ₜ (ℂ × ((Fin r → ℂ) × Y)) :=
        ((properCycle_complex_fin_succ_homeomorph r).prodCongr (Homeomorph.refl Y)).trans
          (Homeomorph.prodAssoc ℂ (Fin r → ℂ) Y)
      have he : e (0, y) = (0, (0, y)) := rfl
      have hdeg : n + 2 * (r + 1) = (n + 2 * r) + 2 := by omega
      rw [hdeg]
      let E := properCycle_local_homology_homeomorph_iso
        (X := TopCat.of ((Fin (r + 1) → ℂ) × Y))
        (Y := TopCat.of (ℂ × ((Fin r → ℂ) × Y))) e (0, y) ((n + 2 * r) + 2)
      rw [he] at E
      exact E ≪≫ properCycle_complex_product_local_homology_iso
        (TopCat.of ((Fin r → ℂ) × Y)) (0, y) (n + 2 * r) ≪≫ ih

end HodgeLean.Foundations.QuotientDuality

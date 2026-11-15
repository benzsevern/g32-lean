import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapRefinementInverse

/-! # Homology equivalences for the specified cap source refinement
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual left refinement is invertible on every original homology group.
Source: properCycle_real_cap_source_refinement_left_quasiIso; Mathlib, Algebra/Homology/QuasiIso.lean.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_refinement_left_isIso
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (properCycle_real_cap_source_refinement Y S T).τ₁ n) := by
  letI := properCycle_real_cap_source_refinement_left_quasiIso Y S T hS hT
  infer_instance

/-- The literal right source refinement is invertible in every positive degree, by its actual connecting square.
Source: properCycle_real_cap_source_refinement_inverse_connecting; properCycle_real_cap_refinement_left_isIso.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_refinement_right_isIso
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (properCycle_real_cap_source_refinement Y S T).τ₃ (n+1)) := by
  letI := properCycle_real_cap_refinement_left_isIso Y S T hS hT n
  exact IsIso.of_isIso_fac_left
    (properCycle_real_cap_source_refinement_inverse_connecting Y S T hS hT n)

/-- The original inverse source connecting map is recovered from the refined half-ray connecting map using the two specified refinement inverses.
Source: properCycle_real_cap_source_refinement_inverse_connecting; CategoryTheory.Iso cancellation.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_refinement_inverse_recovery
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (n : ℕ) :
    letI := properCycle_real_cap_refinement_left_isIso Y S T hS hT n
    letI := properCycle_real_cap_refinement_right_isIso Y S T hS hT n
    inv (HomologicalComplex.homologyMap (properCycle_real_cap_source_refinement Y S T).τ₁ n) ≫
        (properCycle_real_cap_source_adjacent_iso Y S T hS hT n).inv =
      (properCycle_real_cap_target_connecting_iso Y (S ∩ T) (hS.inter hT) n).inv ≫
        inv (HomologicalComplex.homologyMap
          (properCycle_real_cap_source_refinement Y S T).τ₃ (n+1)) := by
  letI := properCycle_real_cap_refinement_left_isIso Y S T hS hT n
  letI := properCycle_real_cap_refinement_right_isIso Y S T hS hT n
  dsimp only
  apply (cancel_epi (HomologicalComplex.homologyMap
    (properCycle_real_cap_source_refinement Y S T).τ₁ n)).mp
  apply (cancel_mono (HomologicalComplex.homologyMap
    (properCycle_real_cap_source_refinement Y S T).τ₃ (n+1))).mp
  simpa only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id,
    Category.comp_id] using
      properCycle_real_cap_source_refinement_inverse_connecting Y S T hS hT n

end HodgeLean.Foundations.QuotientDuality

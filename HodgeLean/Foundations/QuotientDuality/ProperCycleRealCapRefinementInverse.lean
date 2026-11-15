import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapSourceExcision

/-! # Inverse connecting maps under the specified source refinement
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual source connecting isomorphism with its literal adjacent degrees.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_real_cap_middle_isZero.
HC no distance; AV milestone no distance. -/
def properCycle_real_cap_source_adjacent_iso
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (n : ℕ) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    (properCycle_fixed_subcomplex_sequence A P Q).X₃.homology (n+1) ≅
      (properCycle_fixed_subcomplex_sequence A P Q).X₁.homology n := by
  dsimp only
  exact (properCycle_fixed_subcomplex_sequence_shortExact (TopCat.of (ℝ × Y)) _ _ _).δIso
    (n+1) n rfl (properCycle_real_cap_middle_isZero Y S T hS hT (n+1)).1
      (properCycle_real_cap_middle_isZero Y S T hS hT n).1

/-- The two actual inverse connecting maps commute with the source refinement on the original homology objects.
Source: Mathlib, Algebra/Homology/HomologySequence.lean, δ_naturality; properCycle_real_cap_source_refinement_connecting.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_source_refinement_inverse_connecting
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (n : ℕ) :
    (properCycle_real_cap_source_adjacent_iso Y S T hS hT n).inv ≫
        HomologicalComplex.homologyMap (properCycle_real_cap_source_refinement Y S T).τ₃ (n+1) =
      HomologicalComplex.homologyMap (properCycle_real_cap_source_refinement Y S T).τ₁ n ≫
        (properCycle_real_cap_target_connecting_iso Y (S ∩ T) (hS.inter hT) n).inv := by
  let eS := properCycle_real_cap_source_adjacent_iso Y S T hS hT n
  let eT := properCycle_real_cap_target_connecting_iso Y (S ∩ T) (hS.inter hT) n
  have h := properCycle_real_cap_source_refinement_connecting Y S T n
  change eS.hom ≫ _ = _ ≫ eT.hom at h
  change eS.inv ≫ HomologicalComplex.homologyMap
      (properCycle_real_cap_source_refinement Y S T).τ₃ (n+1) =
    HomologicalComplex.homologyMap (properCycle_real_cap_source_refinement Y S T).τ₁ n ≫ eT.inv
  apply (cancel_epi eS.hom).mp
  apply (cancel_mono eT.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Category.comp_id, Iso.inv_hom_id] using h.symm

end HodgeLean.Foundations.QuotientDuality

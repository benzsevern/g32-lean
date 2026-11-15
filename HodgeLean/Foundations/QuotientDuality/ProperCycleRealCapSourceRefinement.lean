import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVRefinement
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapTargetNormalization

/-! # The original source cap sequence under actual support refinement
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original fixed-relative source sequence maps by actual support inclusion to the half-ray sequence on the intersected support.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_fixed_subcomplex_sequence_iso; properCycle_subcomplex_mv_refinement.
HC no distance; AV milestone no distance. -/
def properCycle_real_cap_source_refinement (Y : TopCat.{0}) (S T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    let P' := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ
    let Q' := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ
    properCycle_fixed_subcomplex_sequence A P Q ⟶ properCycle_subcomplex_quotient_sequence P' Q' := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let P' := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ
  let Q' := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ
  have hAP : A ⊔ P ≤ P' := sup_le
    (properCycle_subset_subcomplex_mono X (show Prod.snd ⁻¹' Sᶜ ⊆
      {z : X | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ from fun _ hz hp => hz hp.2.1))
    (properCycle_subset_subcomplex_mono X (show {z : X | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ⊆
      {z : X | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ from fun _ hz hp => hz ⟨hp.1,hp.2.2⟩))
  have hAQ : A ⊔ Q ≤ Q' := sup_le
    (properCycle_subset_subcomplex_mono X (show Prod.snd ⁻¹' Sᶜ ⊆
      {z : X | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ from fun _ hz hp => hz hp.2.1))
    (properCycle_subset_subcomplex_mono X (show {z : X | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ ⊆
      {z : X | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ from fun _ hz hp => hz ⟨hp.1,hp.2.2⟩))
  exact (properCycle_fixed_subcomplex_sequence_iso A P Q).inv ≫
    properCycle_subcomplex_mv_refinement hAP hAQ

/-- The actual cap source refinement retains the specified connecting maps on the original quotient terms.
Source: Mathlib, Algebra/Homology/HomologySequence.lean, δ_naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_source_refinement_connecting
    (Y : TopCat.{0}) (S T : Set Y) (n : ℕ) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    let P' := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ
    let Q' := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ
    (properCycle_fixed_subcomplex_sequence_shortExact X A P Q).δ (n+1) n rfl ≫
        HomologicalComplex.homologyMap (properCycle_real_cap_source_refinement Y S T).τ₁ n =
      HomologicalComplex.homologyMap (properCycle_real_cap_source_refinement Y S T).τ₃ (n+1) ≫
        (properCycle_subcomplex_quotient_sequence_shortExact X P' Q').δ (n+1) n rfl := by
  dsimp only
  exact HomologicalComplex.HomologySequence.δ_naturality
    (properCycle_real_cap_source_refinement Y S T)
    (properCycle_fixed_subcomplex_sequence_shortExact (TopCat.of (ℝ × Y)) _ _ _)
    (properCycle_subcomplex_quotient_sequence_shortExact (TopCat.of (ℝ × Y)) _ _) (n+1) n rfl

end HodgeLean.Foundations.QuotientDuality

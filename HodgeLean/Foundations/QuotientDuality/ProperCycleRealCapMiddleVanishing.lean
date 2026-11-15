import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexOpenExcision
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealShift

/-! # Actual half-ray middle groups in the relative cap suspension -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual fixed-relative and target middle groups in the real cap suspension vanish for arbitrary closed normal and tangential supports.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, half-ray contractions and relative Mayer--Vietoris.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_cap_middle_isZero
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (n : ℕ) :
    let X := TopCat.of (ℝ × Y)
    let A : Set X := Prod.snd ⁻¹' Sᶜ
    let P : Set X := {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q : Set X := {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    IsZero ((properCycle_fixed_subcomplex_sequence
      (subsetSingularSubcomplex X A) (subsetSingularSubcomplex X P) (subsetSingularSubcomplex X Q)).X₂.homology n) ∧
    IsZero ((properCycle_subcomplex_quotient_sequence
      (subsetSingularSubcomplex X P) (subsetSingularSubcomplex X Q)).X₂.homology n) := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let A : Set X := Prod.snd ⁻¹' Sᶜ
  let P : Set X := {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q : Set X := {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  have hAo : IsOpen A := hS.isOpen_compl.preimage continuous_snd
  have hPo : IsOpen P := ((isClosed_le continuous_const continuous_fst).inter
    (hT.preimage continuous_snd)).isOpen_compl
  have hQo : IsOpen Q := ((isClosed_le continuous_fst continuous_const).inter
    (hT.preimage continuous_snd)).isOpen_compl
  have hAP : A ∪ P = {z : ℝ × Y | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ := by
    ext z
    change (z.2 ∉ S ∨ ¬ (0 ≤ z.1 ∧ z.2 ∈ T)) ↔ ¬ (0 ≤ z.1 ∧ (z.2 ∈ S ∧ z.2 ∈ T))
    tauto
  have hAQ : A ∪ Q = {z : ℝ × Y | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ := by
    ext z
    change (z.2 ∉ S ∨ ¬ (z.1 ≤ 0 ∧ z.2 ∈ T)) ↔ ¬ (z.1 ≤ 0 ∧ (z.2 ∈ S ∧ z.2 ∈ T))
    tauto
  have hAP0 : IsZero (RelativeHomology ℚ (TopPair.ofSubset (X := X) (A ∪ P)) n) := by
    rw [hAP]
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (properCycle_upper_half_ray_homology_subsingleton Y (S ∩ T) 0 n)
  have hAQ0 : IsZero (RelativeHomology ℚ (TopPair.ofSubset (X := X) (A ∪ Q)) n) := by
    rw [hAQ]
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (properCycle_lower_half_ray_homology_subsingleton Y (S ∩ T) 0 n)
  constructor
  · exact properCycle_fixed_subcomplex_middle_isZero X A P Q hAo hPo hQo n hAP0 hAQ0
  · apply properCycle_subcomplex_middle_isZero X P Q n
    · exact ModuleCat.isZero_iff_subsingleton.mpr
        (properCycle_upper_half_ray_homology_subsingleton Y T 0 n)
    · exact ModuleCat.isZero_iff_subsingleton.mpr
        (properCycle_lower_half_ray_homology_subsingleton Y T 0 n)

/-- In the actual real half-ray model, original cap bijectivity suspends from the intersection to the union without a supplied middle-vanishing or connecting-square premise.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, the relative cap suspension argument.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_cap_suspension_bijective
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj (TopCat.of (ℝ × Y))) p)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    let X := TopCat.of (ℝ × Y)
    let A : Set X := Prod.snd ⁻¹' Sᶜ
    let P : Set X := {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q : Set X := {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    ∀ hA : AlgebraicTopology.Simplicial.cochainMap ℚ (subsetSingularSubcomplex X A).ι p φ = 0,
      Function.Bijective (properCycle_subcomplex_cap_homology_map (subsetSingularSubcomplex X A)
        (subsetSingularSubcomplex X P ⊓ subsetSingularSubcomplex X Q) p q hp φ hA hφ).hom →
      Function.Bijective (properCycle_subcomplex_cap_homology_map (subsetSingularSubcomplex X A)
        (subsetSingularSubcomplex X P ⊔ subsetSingularSubcomplex X Q) p (q + 1) hp φ hA hφ).hom := by
  dsimp only
  intro hA hc
  apply properCycle_subcomplex_mv_cap_bijective (TopCat.of (ℝ × Y))
    (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ))
    (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ)
    (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ) p q hp φ hA hφ
  · exact (properCycle_real_cap_middle_isZero Y S T hS hT (p + (q + 1))).1
  · exact (properCycle_real_cap_middle_isZero Y S T hS hT (p + q)).1
  · exact (properCycle_real_cap_middle_isZero Y S T hS hT (q + 1)).2
  · exact (properCycle_real_cap_middle_isZero Y S T hS hT q).2
  · exact hc

end HodgeLean.Foundations.QuotientDuality

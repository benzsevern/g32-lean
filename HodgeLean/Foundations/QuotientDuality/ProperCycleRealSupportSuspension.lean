import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadUnionQuotientComparison
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapConnectingIsos

/-! # Literal real half-ray supports for arbitrary base supports
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The intersection of the actual half-ray complements is exactly the inverse image of the base support complement.
Source: Hatcher, Algebraic Topology, section 2.2, real suspension pairs.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_half_ray_support_intersection (Y : Type) (T : Set Y) :
    ({z : ℝ × Y | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ∩ {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ) =
      Prod.snd ⁻¹' Tᶜ := by
  ext z
  change (¬ (0 ≤ z.1 ∧ z.2 ∈ T) ∧ ¬ (z.1 ≤ 0 ∧ z.2 ∈ T)) ↔ z.2 ∉ T
  constructor
  · intro h ht
    rcases le_total 0 z.1 with hz | hz
    · exact h.1 ⟨hz, ht⟩
    · exact h.2 ⟨hz, ht⟩
  · intro hz
    exact ⟨fun h => hz h.2, fun h => hz h.2⟩

/-- The union of the actual half-ray complements is the complement of the zero slice over the base support.
Source: Hatcher, Algebraic Topology, section 2.2, real suspension pairs.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_half_ray_support_union (Y : Type) (T : Set Y) :
    ({z : ℝ × Y | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ∪ {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ) =
      {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ := by
  ext z
  change (¬ (0 ≤ z.1 ∧ z.2 ∈ T) ∨ ¬ (z.1 ≤ 0 ∧ z.2 ∈ T)) ↔
    ¬ (z.1 = 0 ∧ z.2 ∈ T)
  constructor
  · rintro (h | h) ⟨hz, ht⟩ <;> exact h ⟨by simp only [hz, le_refl], ht⟩
  · intro h
    by_cases ht : z.2 ∈ T
    · by_cases hz : 0 ≤ z.1
      · right
        rintro ⟨hz', _⟩
        exact h ⟨le_antisymm hz' hz, ht⟩
      · exact Or.inl (fun h => hz h.1)
    · exact Or.inl (fun h => ht h.2)

/-- The actual left quotient of the half-ray sequence is the original relative complex over the base support complement.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_real_half_ray_support_intersection.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_left_iso (Y : TopCat.{0}) (T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    (properCycle_subcomplex_quotient_sequence P Q).X₁ ≅
      (relativeChainFunctor ℚ).obj
        (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Tᶜ)) := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let P : Set X := {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q : Set X := {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  have hI : subsetSingularSubcomplex X P ⊓ subsetSingularSubcomplex X Q =
      subsetSingularSubcomplex X (Prod.snd ⁻¹' Tᶜ) := by
    rw [← subsetSingularSubcomplex_inter, properCycle_real_half_ray_support_intersection]
  exact properCycle_subcomplex_quotient_iso_of_eq hI ≪≫
    properCycle_subset_subcomplex_relative_iso X (Prod.snd ⁻¹' Tᶜ)

/-- Original open-triad excision identifies the actual right half-ray quotient homology with the original zero-slice relative homology.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_real_half_ray_support_union; properCycle_subset_union_quotient_homology_iso.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_right_iso (Y : TopCat.{0}) (T : Set Y)
    (hT : IsClosed T) (n : ℕ) :
    let X := TopCat.of (ℝ × Y)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    (properCycle_subcomplex_quotient_sequence P Q).X₃.homology n ≅
      RelativeHomology ℚ
        (TopPair.ofSubset (X := X) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) n := by
  dsimp only
  let X := TopCat.of (ℝ × Y)
  let P : Set X := {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q : Set X := {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let e : TopPair.ofSubset (X := X) (P ∪ Q) ≅
      TopPair.ofSubset (X := X) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ :=
    TopPair.isoOfSubset (Homeomorph.refl _) (fun z =>
      (Set.ext_iff.mp (properCycle_real_half_ray_support_union Y T) z).symm)
  have hP : IsOpen P := ((isClosed_le continuous_const continuous_fst).inter
    (hT.preimage continuous_snd)).isOpen_compl
  have hQ : IsOpen Q := ((isClosed_le continuous_fst continuous_const).inter
    (hT.preimage continuous_snd)).isOpen_compl
  exact properCycle_subset_union_quotient_homology_iso X P Q hP hQ n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
      ((relativeChainFunctor ℚ).mapIso e)

/-- The actual real support suspension uses inverse original right excision, the signed connecting map, the original left comparison and literal base projection.
Source: Hatcher, Algebraic Topology, section 2.2, relative real suspension; properCycle_real_cap_target_connecting_iso.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_suspension_iso (Y : TopCat.{0}) (T : Set Y)
    (hT : IsClosed T) (n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) (n+1) ≅
        RelativeHomology ℚ (TopPair.ofSubset (X := Y) Tᶜ) n :=
  (properCycle_real_support_right_iso Y T hT (n+1)).symm ≪≫
    properCycle_real_cap_target_connecting_iso Y T hT n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
      (properCycle_real_support_left_iso Y T) ≪≫
    properCycle_product_support_homology_iso ℝ Y T n

/-- The actual left half-ray comparison retains the literal ambient projection to the base-complement relative chains.
Source: properCycle_subset_subcomplex_relative_projection; TopPair.Homotopy.relativeChainProjection_naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_left_projection (Y : TopCat.{0}) (T : Set Y) :
    let X := TopCat.of (ℝ × Y)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    cokernel.π (SSet.chainComplexMap (P ⊓ Q).ι (ModuleCat.of ℚ ℚ)) ≫
        (properCycle_real_support_left_iso Y T).hom =
      relativeChainProjection ℚ (TopPair.ofSubset (X := X) (Prod.snd ⁻¹' Tᶜ)) := by
  dsimp only
  unfold properCycle_real_support_left_iso
  dsimp only [id_eq]
  rw [Iso.trans_hom, ← Category.assoc]
  dsimp only [properCycle_subcomplex_quotient_iso_of_eq]
  rw [properCycle_subcomplex_quotient_projection, properCycle_subset_subcomplex_relative_projection]

end HodgeLean.Foundations.QuotientDuality

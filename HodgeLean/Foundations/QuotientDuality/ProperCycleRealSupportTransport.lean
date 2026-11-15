import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVFunctoriality
import HodgeLean.Foundations.QuotientDuality.ProperCycleSubsetQuotientFunctoriality
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportRightChain

/-! # Literal base transport for actual real support suspensions
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal product map retains the real suspension coordinate and applies the specified continuous map to the base.
Source: Munkres, Topology, section 19, product maps.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_product_map {X Y : TopCat.{0}} (f : X ⟶ Y) :
    TopCat.of (ℝ × X) ⟶ TopCat.of (ℝ × Y) :=
  TopCat.ofHom ⟨fun z => (z.1, f z.2),
    continuous_fst.prodMk (f.hom.continuous.comp continuous_snd)⟩

/-- Complement-preserving base maps preserve every specified real-coordinate support complement under the literal product map.
Source: Hatcher, Algebraic Topology, section 2.1, maps of relative pairs; properCycle_real_support_product_map.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_product_complement_map
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y)
    (h : Set.MapsTo f Tᶜ Uᶜ) (C : Set ℝ) :
    Set.MapsTo (properCycle_real_support_product_map f)
      {z : ℝ × X | z.1 ∈ C ∧ z.2 ∈ T}ᶜ
      {z : ℝ × Y | z.1 ∈ C ∧ z.2 ∈ U}ᶜ := by
  intro z hz hfu
  by_cases ht : z.2 ∈ T
  · exact hz ⟨hfu.1, ht⟩
  · exact h ht hfu.2

/-- Literal base transport induces the actual morphism of the two signed half-ray quotient sequences.
Source: properCycle_real_support_product_complement_map; properCycle_subset_subcomplex_map; properCycle_subcomplex_mv_morphism.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_sequence_map
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y) (h : Set.MapsTo f Tᶜ Uᶜ) :
    let AX := TopCat.of (ℝ × X)
    let AY := TopCat.of (ℝ × Y)
    properCycle_subcomplex_quotient_sequence
        (subsetSingularSubcomplex AX {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ)
        (subsetSingularSubcomplex AX {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ) ⟶
      properCycle_subcomplex_quotient_sequence
        (subsetSingularSubcomplex AY {z | 0 ≤ z.1 ∧ z.2 ∈ U}ᶜ)
        (subsetSingularSubcomplex AY {z | z.1 ≤ 0 ∧ z.2 ∈ U}ᶜ) := by
  dsimp only
  exact properCycle_subcomplex_mv_morphism (TopCat.toSSet.map (properCycle_real_support_product_map f))
    (subsetSingularSubcomplex (TopCat.of (ℝ × X)) {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ)
    (subsetSingularSubcomplex (TopCat.of (ℝ × X)) {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ)
    (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) {z | 0 ≤ z.1 ∧ z.2 ∈ U}ᶜ)
    (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) {z | z.1 ≤ 0 ∧ z.2 ∈ U}ᶜ)
    (properCycle_subset_subcomplex_map _ _ _
      (properCycle_real_support_product_complement_map f T U h (Set.Ici 0)))
    (properCycle_subset_subcomplex_map _ _ _
      (properCycle_real_support_product_complement_map f T U h (Set.Iic 0)))

/-- The specified signed real half-ray connecting isomorphisms retain their actual naturality under literal base transport.
Source: Mathlib, Algebra/Homology/HomologySequence.lean, δ_naturality; properCycle_real_support_sequence_map.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_transport_connecting
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y)
    (h : Set.MapsTo f Tᶜ Uᶜ) (hT : IsClosed T) (hU : IsClosed U) (n : ℕ) :
    (properCycle_real_cap_target_connecting_iso X T hT n).hom ≫
        HomologicalComplex.homologyMap (properCycle_real_support_sequence_map f T U h).τ₁ n =
      HomologicalComplex.homologyMap (properCycle_real_support_sequence_map f T U h).τ₃ (n+1) ≫
        (properCycle_real_cap_target_connecting_iso Y U hU n).hom := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (properCycle_real_support_sequence_map f T U h)
    (properCycle_subcomplex_quotient_sequence_shortExact (TopCat.of (ℝ × X)) _ _)
    (properCycle_subcomplex_quotient_sequence_shortExact (TopCat.of (ℝ × Y)) _ _) (n+1) n rfl

/-- Literal real-product transport is a map of the actual inverse-image support-complement pairs.
Source: Hatcher, Algebraic Topology, section 2.1, functorial relative pairs.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_normal_pair_map
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y) (h : Set.MapsTo f Tᶜ Uᶜ) :
    TopPair.ofSubset (X := TopCat.of (ℝ × X)) (Prod.snd ⁻¹' Tᶜ) ⟶
      TopPair.ofSubset (X := TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Uᶜ) :=
  TopPair.ofSubsetHom (properCycle_real_support_product_map f) (fun _ hz => h hz)

/-- Literal real-product transport is a map of the actual zero-slice support-complement pairs.
Source: Hatcher, Algebraic Topology, section 2.1, functorial relative pairs; properCycle_real_support_product_complement_map.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_zero_pair_map
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y) (h : Set.MapsTo f Tᶜ Uᶜ) :
    TopPair.ofSubset (X := TopCat.of (ℝ × X)) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ ⟶
      TopPair.ofSubset (X := TopCat.of (ℝ × Y)) {z | z.1 = 0 ∧ z.2 ∈ U}ᶜ :=
  TopPair.ofSubsetHom (properCycle_real_support_product_map f)
    (properCycle_real_support_product_complement_map f T U h {0})

end HodgeLean.Foundations.QuotientDuality

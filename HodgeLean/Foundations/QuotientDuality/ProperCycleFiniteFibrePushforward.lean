import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteLocalClasses
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapNaturality

/-! # Actual local pushforward as a sum over a finite fibre -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original continuous map sends its literal fibre-complement pair to the target point-complement pair.
Source: Hatcher, Algebraic Topology, section 2.1, maps of relative pairs.
HC no distance; AV milestone no distance. -/
def properCycle_fibre_complement_pair_map
    {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) :
    TopPair.ofSubset (X := X) (f ⁻¹' {y})ᶜ ⟶ pointComplementPair y :=
  TopPair.ofSubsetHom f (fun _ hx => hx)

/-- The contribution of one point of an actual finite fibre uses the inverse of the literal finite-localization map and the original map of pairs.
Source: Hatcher, Algebraic Topology, section 2.2, excision and local degree.
HC no distance; AV milestone no distance. -/
def properCycle_finite_fibre_point_pushforward
    {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) [DecidableEq (f ⁻¹' {y})] (n : ℕ)
    (x : f ⁻¹' {y}) : orientationGroup X n x.val →ₗ[ℚ] orientationGroup Y n y :=
  (relativeHomologyMap ℚ n (properCycle_fibre_complement_pair_map f y)).comp
    ((properCycle_finite_support_localization X (f ⁻¹' {y}) hfinite n).symm.toLinearMap.comp
      (LinearMap.single ℚ (fun z : f ⁻¹' {y} => orientationGroup X n z.val) x))

/-- Localizing the actual global pushforward at a target point is the sum of the actual point contributions on its finite fibre.
Source: Hatcher, Algebraic Topology, section 2.2, excision and the sum of local degrees.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_fibre_local_pushforward
    {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) [Fintype (f ⁻¹' {y})] [DecidableEq (f ⁻¹' {y})]
    (n : ℕ) (c : Homology ℚ X n) :
    localOrientation Y n (homologyMap ℚ n f c) y =
      ∑ x : f ⁻¹' {y}, properCycle_finite_fibre_point_pushforward f y hfinite n x
        (localOrientation X n c x.val) := by
  let Q := TopPair.ofSubset (X := X) (f ⁻¹' {y})ᶜ
  let d := (relativeHomologyProjection ℚ Q n).hom c
  have hd := properCycle_finite_support_sum_local_lifts X (f ⁻¹' {y}) hfinite n d
  have hlocal (x : f ⁻¹' {y}) : relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr x.property)) d =
      localOrientation X n c x.val := by
    have hn := properCycle_relative_homology_projection_naturality
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr x.property)) n c
    change relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr x.property)) d =
      (relativeHomologyProjection ℚ (pointComplementPair x.val) n).hom
        (homologyMap ℚ n (𝟙 X) c) at hn
    simpa only [localOrientation, homologyMap_id, LinearMap.id_apply] using hn
  have hpush := properCycle_relative_homology_projection_naturality
    (properCycle_fibre_complement_pair_map f y) n c
  change relativeHomologyMap ℚ n (properCycle_fibre_complement_pair_map f y) d =
    localOrientation Y n (homologyMap ℚ n f c) y at hpush
  rw [← hpush, ← hd, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [hlocal]
  rfl

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeImageVanishing
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodFundamental

/-! # Actual point contributions represented inside isolated support neighborhoods -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual neighborhood meeting a support only at one point maps its point-complement pair to the original support-complement pair.
Source: Hatcher, Algebraic Topology, section 2.2, isolated-support excision.
HC no distance; AV milestone no distance. -/
def properCycle_isolated_support_pair_map
    (X : TopCat.{0}) (S U : Set X) (x : X)
    (hisolate : ∀ z ∈ U, z ∈ S → z = x) :
    neighborhoodSupportComplementPair U ({x} : Set X) ⟶
      TopPair.ofSubset (X := X) Sᶜ :=
  TopPair.ofSubsetHom (TopPair.ofSubset (X := X) U).map (fun z hz hS =>
    hz (hisolate z.val z.property hS))

/-- Restriction of the isolated-neighborhood map at its distinguished point is the literal singleton excision map.
Source: Hatcher, Algebraic Topology, section 2.2, naturality of excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_isolated_support_pair_map_at_point
    (X : TopCat.{0}) (S U : Set X) (x : X) (hxS : x ∈ S)
    (hisolate : ∀ z ∈ U, z ∈ S → z = x) :
    properCycle_isolated_support_pair_map X S U x hisolate ≫
      supportInclusionPairMap X (Set.singleton_subset_iff.mpr hxS) =
      b6m_subspacePairMap X U ({x} : Set X)ᶜ := by
  ext z : 2 <;> rfl

/-- An isolated support neighborhood contributes zero at every other support point under the literal relative restriction.
Source: Hatcher, Algebraic Topology, section 2.2, disjoint support excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_isolated_support_pair_map_other_point
    (X : TopCat.{0}) (S U : Set X) (x z : X) (hzS : z ∈ S) (hzx : z ≠ x)
    (hisolate : ∀ u ∈ U, u ∈ S → u = x) (n : ℕ)
    (c : RelativeHomology ℚ (neighborhoodSupportComplementPair U ({x} : Set X)) n) :
    relativeHomologyMap ℚ n (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hzS))
      (relativeHomologyMap ℚ n (properCycle_isolated_support_pair_map X S U x hisolate) c) = 0 := by
  have hfull : ∀ u : U, (u.val : X) ∈ ({z} : Set X)ᶜ := by
    intro u
    change u.val ≠ z
    intro he
    exact hzx (he.symm.trans (hisolate u.val u.property (he.symm ▸ hzS)))
  let f := (TopPair.ofSubset (X := X) U).map
  let hf : ∀ u ∈ Subtype.val ⁻¹' ({x} : Set X)ᶜ, f u ∈ ({z} : Set X)ᶜ :=
    fun u _ => hfull u
  have hc : properCycle_isolated_support_pair_map X S U x hisolate ≫
      supportInclusionPairMap X (Set.singleton_subset_iff.mpr hzS) =
      TopPair.ofSubsetHom f hf := by
    ext u : 2 <;> rfl
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hc]
  exact properCycle_relative_homology_zero_of_image_in_subspace _ _ f hf hfull n c

/-- The original isolated-neighborhood map represents exactly one coordinate of the actual finite-support localization equivalence.
Source: Hatcher, Algebraic Topology, section 2.2, finite support excision and local contributions.
HC no distance; AV milestone no distance. -/
lemma properCycle_isolated_support_map_localization
    (X : TopCat.{0}) [T2Space X] (S U : Set X) (hS : S.Finite) [DecidableEq S]
    (x : X) (hxS : x ∈ S) (hisolate : ∀ u ∈ U, u ∈ S → u = x) (n : ℕ)
    (c : RelativeHomology ℚ (neighborhoodSupportComplementPair U ({x} : Set X)) n) :
    properCycle_finite_support_localization X S hS n
      (relativeHomologyMap ℚ n (properCycle_isolated_support_pair_map X S U x hisolate) c) =
      Pi.single (⟨x, hxS⟩ : S)
        (relativeHomologyMap ℚ n (b6m_subspacePairMap X U ({x} : Set X)ᶜ) c) := by
  classical
  ext z
  change relativeHomologyMap ℚ n
    (supportInclusionPairMap X (Set.singleton_subset_iff.mpr z.property))
    (relativeHomologyMap ℚ n (properCycle_isolated_support_pair_map X S U x hisolate) c) = _
  by_cases hz : z = (⟨x, hxS⟩ : S)
  · subst z
    rw [Pi.single_eq_same, ← LinearMap.comp_apply, ← relativeHomologyMap_comp,
      properCycle_isolated_support_pair_map_at_point X S U x hxS hisolate]
    rfl
  · have hzx : z.val ≠ x := fun h => hz (Subtype.ext h)
    rw [Pi.single_eq_of_ne hz]
    exact properCycle_isolated_support_pair_map_other_point X S U x z.val z.property hzx hisolate n c

end HodgeLean.Foundations.QuotientDuality

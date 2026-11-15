import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDuality

/-! # Locality of the homological degree calculation

Inclusion of smaller neighbourhoods preserves the excised chart orientation
and the image under an isolated point map.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem isolatedPairMap_restrict {X Y : TopCat.{0}} [T1Space X]
    (f : X ⟶ Y) {V U : Set X} (hVU : V ⊆ U) (x : X)
    (h : ∀ z ∈ U, f z = f x → z = x) :
    neighborhoodSupportInclusionPairMap hVU {x} ≫ isolatedPairMap f U x h =
      isolatedPairMap f V x (fun z hz => h z (hVU hz)) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext z <;> rfl

theorem neighborhoodOrientation_inclusion
    {M : Type} [TopologicalSpace M] [T1Space M] (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    {V U : Set M} (hVU : V ⊆ U) (hV : IsOpen V) (hxV : x ∈ V)
    (hU : IsOpen U) (hxU : x ∈ U) :
    relativeHomologyMap ℚ (2 * d) (neighborhoodSupportInclusionPairMap hVU {x})
      (neighborhoodOrientation d e x hx V hV hxV) =
        neighborhoodOrientation d e x hx U hU hxU := by
  apply (neighborhoodPointComplement_relativeHomologyMap_bijective U x hU hxU (2 * d)).1
  have hcomp : neighborhoodSupportInclusionPairMap hVU {x} ≫
      neighborhoodPointComplementPairMap U x = neighborhoodPointComplementPairMap V x := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext z <;> rfl
  change ((relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap U x)).comp
    (relativeHomologyMap ℚ (2 * d) (neighborhoodSupportInclusionPairMap hVU {x})))
      (neighborhoodOrientation d e x hx V hV hxV) = _
  rw [← relativeHomologyMap_comp, hcomp]
  have hcV := ConcreteCategory.congr_hom
    (Iso.inv_hom_id (neighborhoodPointComplementRelativeHomologyIso V x hV hxV (2 * d)))
    (localClassOfChart d e x hx)
  have hcU := ConcreteCategory.congr_hom
    (Iso.inv_hom_id (neighborhoodPointComplementRelativeHomologyIso U x hU hxU (2 * d)))
    (localClassOfChart d e x hx)
  exact hcV.trans hcU.symm

theorem isolated_orientation_image_restrict
    {M : Type} [TopologicalSpace M] [T1Space M] {Y : TopCat.{0}}
    (f : TopCat.of M ⟶ Y) (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    {V U : Set M} (hVU : V ⊆ U) (hV : IsOpen V) (hxV : x ∈ V)
    (hU : IsOpen U) (hxU : x ∈ U)
    (h : ∀ z ∈ U, f z = f x → z = x) :
    relativeHomologyMap ℚ (2 * d) (isolatedPairMap f U x h)
      (neighborhoodOrientation d e x hx U hU hxU) =
    relativeHomologyMap ℚ (2 * d)
      (isolatedPairMap f V x (fun z hz => h z (hVU hz)))
      (neighborhoodOrientation d e x hx V hV hxV) := by
  rw [← neighborhoodOrientation_inclusion d e x hx hVU hV hxV hU hxU]
  change ((relativeHomologyMap ℚ (2 * d) (isolatedPairMap f U x h)).comp
    (relativeHomologyMap ℚ (2 * d) (neighborhoodSupportInclusionPairMap hVU {x})))
      (neighborhoodOrientation d e x hx V hV hxV) = _
  rw [← relativeHomologyMap_comp, isolatedPairMap_restrict f hVU x h]
  rfl

theorem isolated_orientation_image_neighborhood_independent
    {M : Type} [TopologicalSpace M] [T1Space M] {Y : TopCat.{0}}
    (f : TopCat.of M ⟶ Y) (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    (U V : Set M) (hU : IsOpen U) (hxU : x ∈ U) (hV : IsOpen V) (hxV : x ∈ V)
    (hisoU : ∀ z ∈ U, f z = f x → z = x)
    (hisoV : ∀ z ∈ V, f z = f x → z = x) :
    relativeHomologyMap ℚ (2 * d) (isolatedPairMap f U x hisoU)
      (neighborhoodOrientation d e x hx U hU hxU) =
    relativeHomologyMap ℚ (2 * d) (isolatedPairMap f V x hisoV)
      (neighborhoodOrientation d e x hx V hV hxV) := by
  calc
    _ = relativeHomologyMap ℚ (2 * d)
        (isolatedPairMap f (U ∩ V) x (fun z hz => hisoU z hz.1))
        (neighborhoodOrientation d e x hx (U ∩ V) (hU.inter hV) ⟨hxU, hxV⟩) :=
      isolated_orientation_image_restrict f d e x hx Set.inter_subset_left
        (hU.inter hV) ⟨hxU, hxV⟩ hU hxU hisoU
    _ = _ := (isolated_orientation_image_restrict f d e x hx Set.inter_subset_right
      (hU.inter hV) ⟨hxU, hxV⟩ hV hxV hisoV).symm

end AlgebraicGeometry.SingularCycles

import HodgeLean.Foundations.QuotientDuality.ProperCyclePartialChartLocalHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenPointExcisionInverse

/-! # Original intrinsic chart classes in actual centered point coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal centered chart point map sends inverse original open point excision of its original chart class to the standard complex local class.
Source: properCycle_restricted_chart_local_class_normalization; properCycle_open_local_homology_inverse_map.
HC no distance; AV milestone no distance. -/
lemma properCycle_centered_chart_point_value
    (X : TopCat.{0}) [T1Space X] (r : ℕ)
    (e : OpenPartialHomeomorph X (Fin r → ℂ)) (x : X) (hx : x ∈ e.source) (he : e x = 0) :
    let W : Opens X := ⟨e.source, e.open_source⟩
    let f : TopCat.of W ⟶ TopCat.of (Fin r → ℂ) :=
      TopCat.ofHom ⟨fun u => e u.val, (e.continuousOn.mono (show (W : Set X) ⊆ e.source from Set.Subset.rfl)).domRestrict⟩
    let hf : Set.MapsTo f ({⟨x, hx⟩} : Set W)ᶜ ({0} : Set (Fin r → ℂ))ᶜ :=
      fun u hu hu0 => hu (Subtype.ext (e.injOn u.property hx (hu0.trans he.symm)))
    relativeHomologyMap ℚ (2*r) (TopPair.ofSubsetHom f hf)
      ((properCycle_open_local_homology_iso X W ⟨x, hx⟩ (2*r)).inv.hom
        (localClassOfChart r e x hx)) = standardComplexLocalClass ℚ r := by
  dsimp only
  let W : Opens X := ⟨e.source, e.open_source⟩
  let f : TopCat.of W ⟶ TopCat.of (Fin r → ℂ) :=
    TopCat.ofHom ⟨fun u => e u.val, (e.continuousOn.mono (show (W : Set X) ⊆ e.source from Set.Subset.rfl)).domRestrict⟩
  let p := TopPair.ofSubsetHom f
    (show Set.MapsTo f ({⟨x, hx⟩} : Set W)ᶜ ({0} : Set (Fin r → ℂ))ᶜ from
      fun u hu hu0 => hu (Subtype.ext (e.injOn u.property hx (hu0.trans he.symm))))
  let P : neighborhoodPointComplementPair e.source x ≅ pointComplementPair (⟨x, hx⟩ : W) :=
    TopPair.isoOfSubset (Homeomorph.refl W) (by
      intro u
      change u ≠ ⟨x, hx⟩ ↔ u.val ≠ x
      exact not_congr Subtype.ext_iff)
  let t : pointComplementPair (e x) ⟶ puncturedPair ℂ r :=
    TopPair.ofSubsetHom (𝟙 (TopCat.of (Fin r → ℂ)))
      (fun u hu hu0 => hu (hu0.trans he.symm))
  have hp : properCycle_restricted_chart_point_pair_map r e x hx e.source Set.Subset.rfl ≫ t =
      P.hom ≫ p := by ext u : 2 <;> rfl
  have ht : translationPointComplementPairMap (Fin r → ℂ) (e x) ≫ t = 𝟙 (puncturedPair ℂ r) := by
    ext u : 2
    · apply Subtype.ext
      change u.val + e x = u.val
      rw [he, add_zero]
    · change (show Fin r → ℂ from u) + e x = u
      rw [he, add_zero]
  have h := properCycle_restricted_chart_local_class_normalization r e x hx
    e.source Set.Subset.rfl e.open_source hx
  have hh := congrArg (relativeHomologyMap ℚ (2*r) t) h
  change relativeHomologyMap ℚ (2*r) t (relativeHomologyMap ℚ (2*r) _ _) =
    relativeHomologyMap ℚ (2*r) t (relativeHomologyMap ℚ (2*r) _ _) at hh
  have hpm := congrArg (relativeHomologyMap ℚ (2*r)) hp
  have htm := congrArg (relativeHomologyMap ℚ (2*r)) ht
  simp only [relativeHomologyMap_comp, relativeHomologyMap_id] at hpm htm
  rw [properCycle_open_local_homology_inverse_map]
  change relativeHomologyMap ℚ (2*r) p (relativeHomologyMap ℚ (2*r) P.hom _) = _
  have hleft := LinearMap.congr_fun hpm
    ((neighborhoodPointComplementRelativeHomologyIso e.source x e.open_source hx (2*r)).inv.hom
      (localClassOfChart r e x hx))
  have hright := LinearMap.congr_fun htm (standardComplexLocalClass ℚ r)
  exact hleft.symm.trans (hh.trans hright)

end HodgeLean.Foundations.QuotientDuality

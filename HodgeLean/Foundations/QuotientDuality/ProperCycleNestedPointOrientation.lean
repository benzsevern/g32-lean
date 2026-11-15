import HodgeLean.Foundations.QuotientDuality.ProperCycleNestedPointExcision

/-! # Specified ambient orientations under nested point excision
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Original inverse point excision retains the specified global orientation at an actual identified image point in a larger open neighborhood.
Source: properCycle_nested_point_excision; localOrientation.
HC no distance; AV milestone no distance. -/
lemma properCycle_nested_point_orientation
    (X : TopCat.{0}) [T1Space X] (W V : Opens X) (hWV : W ≤ V)
    (w : W) (v : V) (hv : w.val = v.val) (n : ℕ) (c : Homology ℚ X n) :
    let i : TopCat.of W ⟶ TopCat.of V :=
      TopCat.ofHom ⟨fun x => ⟨x.val, hWV x.property⟩, continuous_subtype_val.subtype_mk _⟩
    let hf : Set.MapsTo i ({w} : Set W)ᶜ ({v} : Set V)ᶜ := fun x hx he =>
      hx (Subtype.ext ((congrArg (fun z : V => z.val) he).trans hv.symm))
    relativeHomologyMap ℚ n (TopPair.ofSubsetHom i hf)
      ((properCycle_open_local_homology_iso X W w n).inv.hom (localOrientation X n c w.val)) =
      (properCycle_open_local_homology_iso X V v n).inv.hom (localOrientation X n c v.val) := by
  let i : TopCat.of W ⟶ TopCat.of V :=
    TopCat.ofHom ⟨fun x => ⟨x.val, hWV x.property⟩, continuous_subtype_val.subtype_mk _⟩
  have he : i w = v := Subtype.ext hv
  subst v
  have hi : Function.Injective i := by
    intro x y h
    have hh := congrArg (fun z : V => z.val) h
    exact Subtype.ext hh
  have h := properCycle_nested_point_excision X W V hWV w n (localOrientation X n c w.val)
  dsimp only at h ⊢
  have hp : imagePointPairMap i hi w = TopPair.ofSubsetHom i
      (show Set.MapsTo i ({w} : Set W)ᶜ ({i w} : Set V)ᶜ from fun x hx he =>
        hx (hi he)) := by ext x : 2 <;> rfl
  change relativeHomologyMap ℚ n (imagePointPairMap i hi w) _ = _ at h
  rw [hp] at h
  exact h

end HodgeLean.Foundations.QuotientDuality

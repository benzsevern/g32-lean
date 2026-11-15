import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenPointExcisionMap

/-! # Inverse point excision on nested actual open neighborhoods
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Inverse original point excision commutes with the actual inclusion of nested open neighborhoods.
Source: properCycle_open_local_homology_iso_map; relativeHomologyMap_comp.
HC no distance; AV milestone no distance. -/
lemma properCycle_nested_point_excision
    (X : TopCat.{0}) [T1Space X] (W V : Opens X) (hWV : W ≤ V)
    (w : W) (n : ℕ) (c : orientationGroup X n w.val) :
    let i : TopCat.of W ⟶ TopCat.of V :=
      TopCat.ofHom ⟨fun x => ⟨x.val, hWV x.property⟩, continuous_subtype_val.subtype_mk _⟩
    relativeHomologyMap ℚ n (imagePointPairMap i
      (by
        intro x y h
        have hv := congrArg (fun z : V => z.val) h
        exact Subtype.ext hv) w)
      ((properCycle_open_local_homology_iso X W w n).inv.hom c) =
    (properCycle_open_local_homology_iso X V (i w) n).inv.hom c := by
  dsimp only
  let i : TopCat.of W ⟶ TopCat.of V :=
    TopCat.ofHom ⟨fun x => ⟨x.val, hWV x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let eW := properCycle_open_local_homology_iso X W w n
  let eV := properCycle_open_local_homology_iso X V (i w) n
  apply eV.toLinearEquiv.injective
  change eV.hom.hom _ = eV.hom.hom (eV.inv.hom c)
  rw [eV.inv_hom_id_apply]
  change (properCycle_open_local_homology_iso X V (i w) n).hom.hom _ = c
  rw [properCycle_open_local_homology_iso_map]
  have hp : imagePointPairMap i
      (by
        intro x y h
        have hv := congrArg (fun z : V => z.val) h
        exact Subtype.ext hv) w ≫
      imagePointPairMap (TopPair.ofSubset (X := X) (V : Set X)).map Subtype.val_injective (i w) =
      imagePointPairMap (TopPair.ofSubset (X := X) (W : Set X)).map Subtype.val_injective w := by
    ext x : 2 <;> rfl
  have hh := congrArg (fun f => relativeHomologyMap ℚ n f (eW.inv.hom c)) hp
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hh
  rw [← properCycle_open_local_homology_iso_map X W w n] at hh
  exact hh.trans (eW.inv_hom_id_apply c)

end HodgeLean.Foundations.QuotientDuality

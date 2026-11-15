import HodgeLean.Foundations.QuotientDuality.ProperCyclePartialChartCap

/-! # Point-complement comparison for actual maps of open triads -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Equal subspaces give the literal identity map on the original relative chain quotients.
Source: Hatcher, Algebraic Topology, section 2.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_subset_transport_map
    {X : TopCat.{0}} (A B : Set X) (h : A = B) :
    (relativeChainFunctor ℚ).map
      (TopPair.ofSubsetHom (𝟙 X) (show Set.MapsTo (𝟙 X) A B from fun _ hx => h ▸ hx)) =
      eqToHom (congrArg (fun U : Set X => (relativeChainFunctor ℚ).obj
        (TopPair.ofSubset (X := X) U)) h) := by
  subst B
  have hi : TopPair.ofSubsetHom (𝟙 X)
      (show Set.MapsTo (𝟙 X) A A from fun _ hx => hx) =
      𝟙 (TopPair.ofSubset (X := X) A) := by ext z : 2 <;> rfl
  rw [hi, (relativeChainFunctor ℚ).map_id]
  rfl

/-- The point-complement comparison retains the original triad map and its actual underlying continuous map.
Source: Hatcher, Algebraic Topology, section 2.2, naturality of excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_point_comparison
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)
    (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C) (hDo : IsOpen D)
    (x : X) (y : Y) (hU : A ∪ B = ({x} : Set X)ᶜ)
    (hV : C ∪ D = ({y} : Set Y)ᶜ)
    (hf : Set.MapsTo f ({x} : Set X)ᶜ ({y} : Set Y)ᶜ) (n : ℕ) :
    HomologicalComplex.homologyMap
        (properCycle_triad_relative_chain_map f A B C D hA hB) n ≫
      (properCycle_triad_local_homology_iso Y C D hCo hDo y hV n).hom =
    (properCycle_triad_local_homology_iso X A B hAo hBo x hU n).hom ≫
      HomologicalComplex.homologyMap
        ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hf)) n := by
  let fU := TopPair.ofSubsetHom f (show Set.MapsTo f (A ∪ B) (C ∪ D) from
    fun _ h => h.elim (fun h => Or.inl (hA h)) (fun h => Or.inr (hB h)))
  let iX := TopPair.ofSubsetHom (𝟙 X)
    (show Set.MapsTo (𝟙 X) (A ∪ B) ({x} : Set X)ᶜ from fun _ h => hU ▸ h)
  let iY := TopPair.ofSubsetHom (𝟙 Y)
    (show Set.MapsTo (𝟙 Y) (C ∪ D) ({y} : Set Y)ᶜ from fun _ h => hV ▸ h)
  have hs : fU ≫ iY = iX ≫ TopPair.ofSubsetHom f hf := by ext z : 2 <;> rfl
  have ht := properCycle_triad_map_union_comparison f A B C D hA hB
  have ht' : properCycle_triad_relative_chain_map f A B C D hA hB ≫
      (triadToUnionRelativeChainMap ℚ Y C D ≫ (relativeChainFunctor ℚ).map iY) =
    (triadToUnionRelativeChainMap ℚ X A B ≫ (relativeChainFunctor ℚ).map iX) ≫
      (relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hf) := by
    rw [← Category.assoc, ht, Category.assoc, ← Functor.map_comp, hs,
      Functor.map_comp, Category.assoc]
  have hh := congrArg (fun m => HomologicalComplex.homologyMap m n) ht'
  simp only [HomologicalComplex.homologyMap_comp] at hh
  unfold properCycle_triad_local_homology_iso
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  dsimp only [iX, iY] at hh
  rw [properCycle_subset_transport_map (C ∪ D) _ hV,
    properCycle_subset_transport_map (A ∪ B) _ hU] at hh
  exact hh

/-- The inverse point-excision comparisons retain the actual induced triad homology map.
Source: Hatcher, Algebraic Topology, section 2.2, naturality of excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_point_inverse_comparison
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)
    (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C) (hDo : IsOpen D)
    (x : X) (y : Y) (hU : A ∪ B = ({x} : Set X)ᶜ)
    (hV : C ∪ D = ({y} : Set Y)ᶜ)
    (hf : Set.MapsTo f ({x} : Set X)ᶜ ({y} : Set Y)ᶜ) (n : ℕ)
    (c : orientationGroup X n x) :
    (HomologicalComplex.homologyMap
        (properCycle_triad_relative_chain_map f A B C D hA hB) n).hom
      ((properCycle_triad_local_homology_iso X A B hAo hBo x hU n).inv.hom c) =
    (properCycle_triad_local_homology_iso Y C D hCo hDo y hV n).inv.hom
      (relativeHomologyMap ℚ n (TopPair.ofSubsetHom f hf) c) := by
  let iX := properCycle_triad_local_homology_iso X A B hAo hBo x hU n
  let iY := properCycle_triad_local_homology_iso Y C D hCo hDo y hV n
  apply (ConcreteCategory.bijective_of_isIso iY.hom).injective
  have hh := ConcreteCategory.congr_hom
    (properCycle_triad_point_comparison f A B C D hA hB hAo hBo hCo hDo x y hU hV hf n)
    (iX.inv.hom c)
  change iY.hom.hom _ = iY.hom.hom (iY.inv.hom _)
  rw [iY.inv_hom_id_apply]
  change iY.hom.hom _ = relativeHomologyMap ℚ n (TopPair.ofSubsetHom f hf) (iX.hom.hom (iX.inv.hom c)) at hh
  rw [iX.inv_hom_id_apply] at hh
  exact hh

/-- Changing a homology degree commutes with the literal induced map of pairs.
Source: Hatcher, Algebraic Topology, section 2.1, functorial homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_homology_degree_iso_map
    {P Q : TopPair.{0}} (f : P ⟶ Q) (n m : ℕ) (h : n = m)
    (c : RelativeHomology ℚ P n) :
    relativeHomologyMap ℚ m f
        ((eqToIso (congrArg (fun j => RelativeHomology ℚ P j) h)).hom.hom c) =
      (eqToIso (congrArg (fun j => RelativeHomology ℚ Q j) h)).hom.hom
        (relativeHomologyMap ℚ n f c) := by
  subst m
  rfl

end HodgeLean.Foundations.QuotientDuality

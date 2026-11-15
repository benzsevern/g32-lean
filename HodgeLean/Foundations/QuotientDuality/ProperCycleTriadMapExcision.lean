import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadCapHomologyNaturality

/-! # Actual triad maps under the original union-relative comparison -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original triad map commutes with the literal union-relative comparison for every actual map preserving both subspaces.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, naturality of triad excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_map_union_comparison
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) :
    let fU := TopPair.ofSubsetHom f (show Set.MapsTo f (A ∪ B) (C ∪ D) from
      fun _ h => h.elim (fun h => Or.inl (hA h)) (fun h => Or.inr (hB h)))
    properCycle_triad_relative_chain_map f A B C D hA hB ≫ triadToUnionRelativeChainMap ℚ Y C D =
      triadToUnionRelativeChainMap ℚ X A B ≫ (relativeChainFunctor ℚ).map fU := by
  dsimp only
  let fU := TopPair.ofSubsetHom f (show Set.MapsTo f (A ∪ B) (C ∪ D) from
    fun _ h => h.elim (fun h => Or.inl (hA h)) (fun h => Or.inr (hB h)))
  have hn := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) fU
  letI : Epi (triadRelativeChainProjection ℚ X A B) := by
    change Epi (cokernel.π _)
    infer_instance
  apply (cancel_epi (triadRelativeChainProjection ℚ X A B)).mp
  calc
    _ = SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) ≫
        triadRelativeChainProjection ℚ Y C D ≫ triadToUnionRelativeChainMap ℚ Y C D := by
      rw [← Category.assoc, properCycle_triad_relative_chain_projection_naturality, Category.assoc]
    _ = SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) ≫
        relativeChainProjection ℚ (TopPair.ofSubset (X := Y) (C ∪ D)) := by
      rw [triadRelativeChainProjection_triadToUnionRelativeChainMap]
    _ = relativeChainProjection ℚ (TopPair.ofSubset (X := X) (A ∪ B)) ≫
        (relativeChainFunctor ℚ).map fU := hn.symm
    _ = _ := by rw [← Category.assoc, triadRelativeChainProjection_triadToUnionRelativeChainMap]

/-- The actual triad homology map is bijective whenever the literal union-relative map is bijective and the original open-triad excision comparisons apply.
Source: Hatcher, Algebraic Topology, section 2.2, natural excision for maps of triads.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_homology_bijective_of_union
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)
    (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C) (hDo : IsOpen D) (n : ℕ) :
    let fU := TopPair.ofSubsetHom f (show Set.MapsTo f (A ∪ B) (C ∪ D) from
      fun _ h => h.elim (fun h => Or.inl (hA h)) (fun h => Or.inr (hB h)))
    Function.Bijective (relativeHomologyMap ℚ n fU) →
      Function.Bijective (HomologicalComplex.homologyMap
        (properCycle_triad_relative_chain_map f A B C D hA hB) n).hom := by
  dsimp only
  intro hc
  let fU := TopPair.ofSubsetHom f (show Set.MapsTo f (A ∪ B) (C ∪ D) from
    fun _ h => h.elim (fun h => Or.inl (hA h)) (fun h => Or.inr (hB h)))
  let eX := triadUnionExcisionHomologyEquiv ℚ X A B n
    (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hAo hBo)
  let eY := triadUnionExcisionHomologyEquiv ℚ Y C D n
    (triadToUnionRelativeChainMap_quasiIso_of_isOpen Y C D hCo hDo)
  have h := congrArg (fun m => HomologicalComplex.homologyMap m n)
    (properCycle_triad_map_union_comparison f A B C D hA hB)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  have hs (c : TriadRelativeHomology ℚ X A B n) :
      eY ((HomologicalComplex.homologyMap (properCycle_triad_relative_chain_map f A B C D hA hB) n).hom c) =
        relativeHomologyMap ℚ n fU (eX c) := by
    exact ConcreteCategory.congr_hom h c
  constructor
  · intro a b hab
    apply eX.injective
    apply hc.1
    rw [← hs a, ← hs b, hab]
  · intro y
    obtain ⟨z, hz⟩ := hc.2 (eY y)
    obtain ⟨x, hx⟩ := eX.surjective z
    refine ⟨x, eY.injective ?_⟩
    rw [hs, hx, hz]

end HodgeLean.Foundations.QuotientDuality

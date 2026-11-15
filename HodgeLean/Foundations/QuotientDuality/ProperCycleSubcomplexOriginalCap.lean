import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexTriadModels

/-! # Original relative cocycles and caps in the subcomplex chain models -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An original relative cochain vanishes on the literal singular image subcomplex of its original subspace.
Source: Hatcher, Algebraic Topology, section 3.1, relative cochains and chain projections.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_cochain_subcomplex_zero
    (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p) :
    AlgebraicTopology.Simplicial.cochainMap ℚ (subsetSingularSubcomplex X A).ι p
      (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ) = 0 := by
  have hz : SSet.chainComplexMap (subsetSingularSubcomplex X A).ι (ModuleCat.of ℚ ℚ) ≫
      relativeChainProjection ℚ (TopPair.ofSubset (X := X) A) = 0 := by
    rw [← properCycle_subset_subcomplex_relative_projection X A,
      ← Category.assoc, cokernel.condition, zero_comp]
  have hp := congrArg (fun m => m.f p) hz
  rw [HomologicalComplex.comp_f] at hp
  ext c
  change φ (((relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f p).hom
    (((SSet.chainComplexMap (subsetSingularSubcomplex X A).ι (ModuleCat.of ℚ ℚ)).f p).hom c)) = 0
  have hc := ConcreteCategory.congr_hom hp c
  change ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f p).hom
    (((SSet.chainComplexMap (subsetSingularSubcomplex X A).ι (ModuleCat.of ℚ ℚ)).f p).hom c) = 0 at hc
  rw [hc, map_zero]

/-- The descended singular subcomplex cap is the original triad cap through the constructed quotient isomorphisms.
Source: Hatcher, Algebraic Topology, section 3.3, original triad cap representatives.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_original_triad_cap
    (X : TopCat.{0}) (A T : Set X) (p q : ℕ)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p) :
    (properCycle_subset_union_subcomplex_triad_iso X A T).inv.f (p + q) ≫
        properCycle_subcomplex_cap_hom (subsetSingularSubcomplex X A) (subsetSingularSubcomplex X T) p q
          (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ)
          (properCycle_relative_cochain_subcomplex_zero X A p φ) ≫
        (properCycle_subset_subcomplex_relative_iso X T).hom.f q =
      triadCapHom ℚ X A T p q φ := by
  have hs : triadRelativeChainProjection ℚ X A T ≫
      (properCycle_subset_union_subcomplex_triad_iso X A T).inv =
        cokernel.π (SSet.chainComplexMap
          (subsetSingularSubcomplex X A ⊔ subsetSingularSubcomplex X T).ι (ModuleCat.of ℚ ℚ)) := by
    rw [← properCycle_subset_union_subcomplex_triad_projection X A T,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hs' := congrArg (fun m => m.f (p + q)) hs
  have ht := congrArg (fun m => m.f q) (properCycle_subset_subcomplex_relative_projection X T)
  rw [HomologicalComplex.comp_f] at hs' ht
  apply Cofork.IsColimit.hom_ext (triadRelativeChainProjectionComponentIsCokernel ℚ X A T (p + q))
  change (triadRelativeChainProjection ℚ X A T).f (p + q) ≫
      ((properCycle_subset_union_subcomplex_triad_iso X A T).inv.f (p + q) ≫ _ ≫ _) =
    (triadRelativeChainProjection ℚ X A T).f (p + q) ≫ triadCapHom ℚ X A T p q φ
  rw [← Category.assoc, hs', ← Category.assoc, properCycle_subcomplex_cap_projection,
    Category.assoc, ht, triadRelativeChainProjection_triadCapHom]
  rfl

/-- The actual even quotient cap chain map is the original triad cap chain map through the original quotient comparisons.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap chain maps.
HC no distance; AV milestone no distance. -/
lemma properCycle_even_subcomplex_original_triad_cap
    (X : TopCat.{0}) (A T : Set X) (p : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0) :
    let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
      ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ, by
        change AlgebraicTopology.Simplicial.coboundary ℚ p _ = 0
        exact (relativeCochainToAbsolute_coboundary ℚ (TopPair.ofSubset (X := X) A) p φ).symm.trans
          ((congrArg (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) (p + 1)) hφ).trans
            (map_zero _))⟩
    HomologicalComplex.restrictionMap (properCycle_subset_union_subcomplex_triad_iso X A T).inv
        (properCycle_cap_tail_embedding p) ≫
      properCycle_even_subcomplex_cap_chain_map (subsetSingularSubcomplex X A)
        (subsetSingularSubcomplex X T) p hp ψ.1
        (properCycle_relative_cochain_subcomplex_zero X A p φ) ψ.2 ≫
      (properCycle_subset_subcomplex_relative_iso X T).hom =
        properCycle_even_triad_cap_chain_map X A T p hp φ hφ := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro q
  exact properCycle_subcomplex_original_triad_cap X A T p q φ

/-- The cap on subcomplex quotient homology is exactly the original triad cap through the actual original quotient comparisons in every degree.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap and original homology comparisons.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_original_triad_cap_homology
    (X : TopCat.{0}) (A T : Set X) (p q : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0) :
    let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
      ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ, by
        change AlgebraicTopology.Simplicial.coboundary ℚ p _ = 0
        exact (relativeCochainToAbsolute_coboundary ℚ (TopPair.ofSubset (X := X) A) p φ).symm.trans
          ((congrArg (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) (p + 1)) hφ).trans
            (map_zero _))⟩
    HomologicalComplex.homologyMap (properCycle_subset_union_subcomplex_triad_iso X A T).inv (p + q) ≫
        properCycle_subcomplex_cap_homology_map (subsetSingularSubcomplex X A) (subsetSingularSubcomplex X T)
          p q hp ψ.1 (properCycle_relative_cochain_subcomplex_zero X A p φ) ψ.2 ≫
        HomologicalComplex.homologyMap (properCycle_subset_subcomplex_relative_iso X T).hom q =
      ModuleCat.ofHom (triadCapHomologyMap ℚ X A T p q φ hφ) := by
  dsimp only
  let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
    ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ, by
      change AlgebraicTopology.Simplicial.coboundary ℚ p _ = 0
      exact (relativeCochainToAbsolute_coboundary ℚ (TopPair.ofSubset (X := X) A) p φ).symm.trans
        ((congrArg (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) (p + 1)) hφ).trans
          (map_zero _))⟩
  have hc := congrArg (fun f => HomologicalComplex.homologyMap f q)
    (properCycle_even_subcomplex_original_triad_cap X A T p hp φ hφ)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hc
  have hn := properCycle_cap_tail_homology_map_naturality
    (properCycle_subset_union_subcomplex_triad_iso X A T).inv p q
  have ho : properCycle_cap_tail_homology_map (triadRelativeChainComplex ℚ X A T) p q ≫
      HomologicalComplex.homologyMap (properCycle_even_triad_cap_chain_map X A T p hp φ hφ) q =
        ModuleCat.ofHom (triadCapHomologyMap ℚ X A T p q φ hφ) := by
    cases q with
    | zero => exact properCycle_even_triad_cap_zero_homology_comparison X A T p hp φ hφ
    | succ q => exact properCycle_even_triad_cap_homology_comparison X A T p q hp φ hφ
  dsimp only [properCycle_subcomplex_cap_homology_map]
  simp only [← Category.assoc]
  erw [hn]
  simp only [Category.assoc]
  erw [hc]
  exact ho

end HodgeLean.Foundations.QuotientDuality

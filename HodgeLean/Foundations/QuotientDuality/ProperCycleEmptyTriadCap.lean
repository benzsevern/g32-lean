import HodgeLean.Foundations.QuotientDuality.ProperCycleEmptyTriad
import HodgeLean.Foundations.QuotientDuality.ProperCycleEvenRelativeCap

/-! # The original empty-triad cap and the original same-pair cap -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original triad cap with empty second subspace is the original same-pair cap followed by its actual empty-relative projection.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_empty_triad_cap_comparison
    (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p) :
    (properCycle_empty_triad_relative_iso X A).hom.f (p + q) ≫
        relativeCapHom ℚ (TopPair.ofSubset (X := X) A) p q φ ≫
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (∅ : Set X))).f q =
      triadCapHom ℚ X A ∅ p q φ := by
  apply Cofork.IsColimit.hom_ext
    (triadRelativeChainProjectionComponentIsCokernel ℚ X A ∅ (p + q))
  have h := congrArg (fun f => f.f (p + q)) (properCycle_empty_triad_relative_projection X A)
  rw [HomologicalComplex.comp_f] at h
  change (triadRelativeChainProjection ℚ X A ∅).f (p + q) ≫
      ((properCycle_empty_triad_relative_iso X A).hom.f (p + q) ≫ _ ≫ _) =
    (triadRelativeChainProjection ℚ X A ∅).f (p + q) ≫ _
  rw [← Category.assoc, ← Category.assoc, h, relativeChainProjection_relativeCapHom,
    triadRelativeChainProjection_triadCapHom]
  rfl

/-- The actual even empty-triad chain cap is the original same-pair chain cap through the literal relative comparisons.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_even_empty_triad_cap_comparison
    (X : TopCat.{0}) (A : Set X) (p : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0) :
    HomologicalComplex.restrictionMap (properCycle_empty_triad_relative_iso X A).hom
        (properCycle_cap_tail_embedding p) ≫
      properCycle_even_relative_cap_chain_map (TopPair.ofSubset (X := X) A) p hp φ hφ ≫
      relativeChainProjection ℚ (TopPair.ofSubset (X := X) (∅ : Set X)) =
        properCycle_even_triad_cap_chain_map X A ∅ p hp φ hφ := by
  apply HomologicalComplex.hom_ext
  intro q
  exact properCycle_empty_triad_cap_comparison X A p q φ

/-- The original empty-triad cap on homology agrees with the original same-pair cap through the literal source and target homology isomorphisms in every degree.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_empty_triad_cap_homology_comparison
    (X : TopCat.{0}) (A : Set X) (p q : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0) :
    HomologicalComplex.homologyMap (properCycle_empty_triad_relative_iso X A).hom (p + q) ≫
        ModuleCat.ofHom (relativeCapHomologyMap ℚ (TopPair.ofSubset (X := X) A) p q φ hφ) ≫
        HomologicalComplex.homologyMap (relativeChainProjection ℚ
          (TopPair.ofSubset (X := X) (∅ : Set X))) q =
      ModuleCat.ofHom (triadCapHomologyMap ℚ X A ∅ p q φ hφ) := by
  have hrel : properCycle_cap_tail_homology_map
      ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) A)) p q ≫
        HomologicalComplex.homologyMap
          (properCycle_even_relative_cap_chain_map (TopPair.ofSubset (X := X) A) p hp φ hφ) q =
      ModuleCat.ofHom (relativeCapHomologyMap ℚ (TopPair.ofSubset (X := X) A) p q φ hφ) := by
    cases q with
    | zero => exact properCycle_even_relative_cap_zero_homology_comparison _ p hp φ hφ
    | succ q => exact properCycle_even_relative_cap_homology_comparison _ p q hp φ hφ
  have hc := congrArg (fun f => HomologicalComplex.homologyMap f q)
    (properCycle_even_empty_triad_cap_comparison X A p hp φ hφ)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hc
  erw [← hrel]
  simp only [← Category.assoc]
  rw [properCycle_cap_tail_homology_map_naturality]
  simp only [Category.assoc]
  rw [hc]
  cases q with
  | zero => exact properCycle_even_triad_cap_zero_homology_comparison X A ∅ p hp φ hφ
  | succ q => exact properCycle_even_triad_cap_homology_comparison X A ∅ p q hp φ hφ

end HodgeLean.Foundations.QuotientDuality

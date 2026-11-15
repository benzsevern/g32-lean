import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSupport

/-! # Relative contractions into the support complement -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular Topology
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A pair map whose entire ambient image lies in the target subspace induces the zero relative chain map.
Source: Hatcher, Algebraic Topology, section 2.1, relative chains as quotient chains.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_chain_map_zero_of_range
    {X Y : TopCat.{0}} (A : Set X) (B : Set Y)
    (f : TopPair.ofSubset A ⟶ TopPair.ofSubset B)
    (hf : ∀ x : X, (TopPair.Hom.fst f) x ∈ B) :
    (relativeChainFunctor ℚ).map f = 0 := by
  let g : X ⟶ TopCat.of B := TopCat.ofHom
    ⟨fun x => ⟨(TopPair.Hom.fst f) x, hf x⟩,
      (TopPair.Hom.fst f).hom.continuous.subtype_mk _⟩
  have hfactor : g ≫ topologicalSubsetInclusion Y B = TopPair.Hom.fst f := rfl
  let C := (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  letI : Epi (relativeChainProjection ℚ (TopPair.ofSubset A)) := by
    dsimp [relativeChainProjection]
    infer_instance
  apply (cancel_epi (relativeChainProjection ℚ (TopPair.ofSubset A))).mp
  rw [comp_zero, TopPair.Homotopy.relativeChainProjection_naturality]
  rw [← hfactor, C.map_comp, Category.assoc]
  exact (congrArg (fun z => C.map g ≫ z)
    (subspaceChainMap_relativeChainProjection (R := ℚ) (TopPair.ofSubset B))).trans
      (by simp only [comp_zero])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A homotopy of pairs from an image in the subspace to the identity makes relative homology vanish.
Source: Hatcher, Algebraic Topology, section 2.1, homotopy invariance of relative homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_homology_subsingleton_of_contraction
    (X : TopCat.{0}) (A : Set X)
    (f : TopPair.ofSubset A ⟶ TopPair.ofSubset A)
    (hf : ∀ x : X, (TopPair.Hom.fst f) x ∈ A)
    (H : TopPair.Homotopy f (𝟙 (TopPair.ofSubset A))) (n : ℕ) :
    Subsingleton (RelativeHomology ℚ (TopPair.ofSubset A) n) := by
  have he := (H.relativeChainHomotopy (R := ℚ)).homologyMap_eq n
  rw [properCycle_relative_chain_map_zero_of_range A A f hf,
    HomologicalComplex.homologyMap_zero, (relativeChainFunctor ℚ).map_id,
    HomologicalComplex.homologyMap_id] at he
  exact ModuleCat.subsingleton_of_isZero ((IsZero.iff_id_eq_zero _).mpr he.symm)


end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.BundleThom.SubsetRelativeComparisonHelpers

/-! # Actual relative domain maps and singular range naturality -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Actual inclusion of relative domain pairs for a supplied subset inclusion.
Source: Hatcher, Algebraic Topology, §2.1, maps of pairs. -/
def i1_subsetRelativePairMap (X : TopCat) (Z : Set X) {U V : Set X} (h : U ⊆ V) :
    i1_subsetRelativePair X Z U ⟶ i1_subsetRelativePair X Z V :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩) (fun _ hz => hz)

/-- Singular ranges preserve actual subset inclusions.
Source: Hatcher, Algebraic Topology, §2.1, singular simplices in subspaces. -/
theorem i1_singularSubsetRange_mono (X : TopCat) {U V : Set X} (h : U ⊆ V) :
    i1_singularSubsetRange X U ≤ i1_singularSubsetRange X V := by
  intro n σ hσ
  rw [i1_mem_singularSubsetRange_iff] at hσ ⊢
  exact fun t => h (hσ t)

/-- The actual domain pair inclusions compose to the specified ambient inclusion.
Source: Hatcher, Algebraic Topology, §2.1, functorial maps of pairs. -/
theorem i1_subsetRelativePairMap_comp_inclusion (X : TopCat) (Z : Set X)
    {U V : Set X} (h : U ⊆ V) :
    i1_subsetRelativePairMap X Z h ≫ i1_subsetRelativePairInclusion X Z V =
      i1_subsetRelativePairInclusion X Z U := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- Actual relative chain coordinates commute with each supplied nested domain inclusion.
Source: Hatcher, Algebraic Topology, §2.2, naturality of relative singular chains. -/
theorem i1_subsetRelativeChainArrowIso_naturality (X : TopCat) (Z : Set X)
    {U V : Set X} (h : U ⊆ V) :
    (chainPairFunctor ℚ).map (i1_subsetRelativePairMap X Z h) ≫
      (i1_subsetRelativeChainArrowIso X Z V).hom =
    (i1_subsetRelativeChainArrowIso X Z U).hom ≫
      (i1_relativeSubcomplexArrowFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).map
        (homOfLE (i1_singularSubsetRange_mono X h)) := by
  apply Arrow.hom_ext
  · change SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _ =
      SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
  · change SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _ =
      SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1

end HodgeLean.Foundations.BundleThom

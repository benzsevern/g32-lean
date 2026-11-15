import HodgeLean.Foundations.BundleThom.SubsetRelativeNaturalityHelpers

/-! # Naturality of actual domain coclass coordinates -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Actual relative chain coordinates commute with a nested domain inclusion after taking cokernels.
Source: Hatcher, Algebraic Topology, §2.2, relative-chain naturality. -/
theorem i1_subsetRelativeChainIso_naturality (X : TopCat) (Z : Set X)
    {U V : Set X} (h : U ⊆ V) :
    (relativeChainFunctor ℚ).map (i1_subsetRelativePairMap X Z h) ≫
      (i1_subsetRelativeChainIso X Z V).hom =
    (i1_subsetRelativeChainIso X Z U).hom ≫
      (i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).map
        (homOfLE (i1_singularSubsetRange_mono X h)) := by
  change (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map _ ≫
    (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map _ =
    (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map _ ≫
      (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    i1_subsetRelativeChainArrowIso_naturality]

/-- Actual nested domain restrictions agree with restriction in the ambient singular-range coordinates.
Source: Hatcher, Algebraic Topology, §3.1, naturality of relative cohomology. -/
theorem i1_subsetRelativeCoclassEquiv_naturality (X : TopCat) (Z : Set X)
    {U V : Set X} (h : U ⊆ V) (n : ℕ)
    (v : RelativeCohomology ℚ (i1_subsetRelativePair X Z V) n) :
    i1_subsetRelativeCoclassEquiv X Z U n
      (relativeCohomologyMap ℚ n (i1_subsetRelativePairMap X Z h) v) =
    i1_chainDualPullback n
      ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).map
        (homOfLE (i1_singularSubsetRange_mono X h)))
      (i1_subsetRelativeCoclassEquiv X Z V n v) := by
  have hf : (i1_subsetRelativeChainIso X Z U).inv ≫
      (relativeChainFunctor ℚ).map (i1_subsetRelativePairMap X Z h) =
    (i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).map
      (homOfLE (i1_singularSubsetRange_mono X h)) ≫ (i1_subsetRelativeChainIso X Z V).inv := by
    apply (cancel_mono (i1_subsetRelativeChainIso X Z V).hom).mp
    rw [Category.assoc, i1_subsetRelativeChainIso_naturality,
      Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change i1_chainDualPullback n (i1_subsetRelativeChainIso X Z U).inv
    (i1_chainDualPullback n ((relativeChainFunctor ℚ).map (i1_subsetRelativePairMap X Z h)) v) =
    i1_chainDualPullback n _ (i1_chainDualPullback n (i1_subsetRelativeChainIso X Z V).inv v)
  rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, hf,
    i1_chainDualPullback_comp, LinearMap.comp_apply]

end HodgeLean.Foundations.BundleThom

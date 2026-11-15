import HodgeLean.RealDefs.FundamentalClass.Chart
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.HomologyZeroNaturality
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

/-! # `[X] = 1`: the point computation (`c = 0`)

The constant class `1 ∈ H^0(X, ∅; ℚ)` is defined through duality with homology:
`augmentationClass P` is the class whose pairing with `H_0` is the augmentation
`singularHomology₀ε`, for a pair `P` with empty subspace. It is natural for maps of pairs
(`relativeCohomologyMap_augmentationClass`). The normalized class of `(ℂ⁰, ℂ⁰ \ {0}) = (pt, ∅)` is
that class (`normalizedPointCoclass_zero`), since upstream's orientation class has augmentation `1`
and spans `H_0`. So the full-support coclass of normal dimension `0` is the constant class
(`fullSupportCoclass_zero_eq_augmentationClass`). -/

open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular Simplicial Convexity

namespace HodgeLean.RealDefs

section Augmentation

variable (P : TopPair)

/-- A pair whose subspace is empty has no singular simplices in it. -/
lemma isEmpty_toSSet_snd (h : IsEmpty P.snd) (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj P.snd) _⦋n⦌) :=
  ⟨fun σ => h.false ((P.snd.toSSetObjEquiv _ σ) StdSimplex.barycenter)⟩

/-- For a pair with empty subspace, the relative chain projection is an isomorphism. -/
lemma isIso_relativeChainProjection (h : IsEmpty P.snd) :
    IsIso (relativeChainProjection ℚ P) := by
  have h0 : ((chainPairFunctor ℚ).obj P).hom = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    apply SSet.chainComplex_hom_ext
    intro σ
    exact (isEmpty_toSSet_snd P h n).false σ |>.elim
  exact cokernel.π_of_zero h0

/-- The augmentation on `H_0(X, ∅; ℚ)`, through the projection from absolute homology. -/
noncomputable def augmentationFunctional [IsIso (relativeChainProjection ℚ P)] :
    Module.Dual ℚ (RelativeHomology ℚ P 0) :=
  ((HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ P)) 0).inv ≫
    P.fst.singularHomology₀ε (ModuleCat.of ℚ ℚ)).hom

/-- The constant class `1 ∈ H^0(X, ∅; ℚ)`: the class whose pairing with `H_0` is the
augmentation. -/
noncomputable def augmentationClass [IsIso (relativeChainProjection ℚ P)] :
    RelativeCohomology ℚ P 0 :=
  (relativeCohomologyEquivDualHomology ℚ P 0).symm (augmentationFunctional P)

variable {P} {Q : TopPair} [IsIso (relativeChainProjection ℚ P)]
  [IsIso (relativeChainProjection ℚ Q)]

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation is natural for maps of pairs with empty subspaces. -/
lemma augmentationFunctional_comp (f : P ⟶ Q) :
    (relativeHomologyFunctor ℚ 0).map f ≫
        (HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ Q)) 0).inv ≫
          Q.fst.singularHomology₀ε (ModuleCat.of ℚ ℚ) =
      (HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ P)) 0).inv ≫
        P.fst.singularHomology₀ε (ModuleCat.of ℚ ℚ) := by
  rw [← cancel_epi (HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ P)) 0).hom,
    Iso.hom_inv_id_assoc, HomologicalComplex.homologyMapIso_hom, asIso_hom]
  change HomologicalComplex.homologyMap _ 0 ≫ HomologicalComplex.homologyMap
    ((relativeChainFunctor ℚ).map f) 0 ≫ _ = _
  rw [← HomologicalComplex.homologyMap_comp_assoc,
    TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f,
    HomologicalComplex.homologyMap_comp_assoc]
  have : HomologicalComplex.homologyMap (relativeChainProjection ℚ Q) 0 ≫
      (HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ Q)) 0).inv = 𝟙 _ :=
    (HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ Q)) 0).hom_inv_id
  rw [reassoc_of% this]
  exact TopCat.singularHomology₀ε_naturality (TopPair.Hom.fst f) (ModuleCat.of ℚ ℚ)

/-- The augmentation is natural for maps of pairs with empty subspaces. -/
lemma augmentationFunctional_relativeHomologyMap (f : P ⟶ Q) (z : RelativeHomology ℚ P 0) :
    augmentationFunctional Q (relativeHomologyMap ℚ 0 f z) = augmentationFunctional P z :=
  ConcreteCategory.congr_hom (augmentationFunctional_comp f) z

/-- Pulling back the constant class gives the constant class. -/
lemma relativeCohomologyMap_augmentationClass (f : P ⟶ Q) :
    relativeCohomologyMap ℚ 0 f (augmentationClass Q) = augmentationClass P := by
  apply (relativeCohomologyEquivDualHomology ℚ P 0).injective
  ext z
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap, augmentationClass,
    augmentationClass, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact augmentationFunctional_relativeHomologyMap f z

end Augmentation

section Point

instance (𝕜 : Type) [Field 𝕜] [TopologicalSpace 𝕜] :
    IsIso (relativeChainProjection ℚ (puncturedPair 𝕜 0)) :=
  isIso_relativeChainProjection _ ⟨fun v => v.2 (funext fun k => k.elim0)⟩

/-- The augmentation evaluates the complex orientation class of `(ℂ⁰, ∅)` to `1`. -/
lemma augmentationFunctional_standardComplexLocalClass_zero :
    augmentationFunctional (puncturedPair ℂ 0) (standardComplexLocalClass ℚ 0) = 1 := by
  have h := augmentationFunctional_relativeHomologyMap (P := puncturedPair ℂ 0)
    (Q := puncturedPair ℝ 0) (standardComplexRealPairIso 0).hom (standardComplexLocalClass ℚ 0)
  refine h.symm.trans ?_
  have hσ : relativeHomologyMap ℚ 0 (standardComplexRealPairIso 0).hom
      (standardComplexLocalClass ℚ 0) = standardLocalClass ℚ 0 :=
    standardComplexRealRelativeHomologyIso_hom_standardComplexLocalClassMul 0
  rw [hσ]
  exact standardLocalClass_zero_epsilon

/-- The normalized class of `(ℂ⁰, ∅)` is the constant class: `c = 0` in the note. -/
theorem normalizedPointCoclass_zero :
    normalizedPointCoclass 0 = augmentationClass (puncturedPair ℂ 0) := by
  apply (relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ 0) 0).injective
  rw [augmentationClass, LinearEquiv.apply_symm_apply]
  change (relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ 0) 0)
    ((relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ 0) 0).symm
      (normalizedDual (standardComplexLocalClass ℚ 0) _)) = _
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext_on (s := {standardComplexLocalClass ℚ 0})
    span_standardComplexLocalClass_zero_eq_top ?_
  rintro _ rfl
  rw [augmentationFunctional_standardComplexLocalClass_zero]
  exact Classical.choose_spec (Module.Projective.exists_dual_eq_one ℚ
    (standardComplexLocalClass_ne_zero_for_chart 0))

/-- `(W, W \ S)` has empty subspace when `W ⊆ S`. -/
lemma isIso_relativeChainProjection_of_subset {M : Type} [TopologicalSpace M] (W S : Set M)
    (hWS : W ⊆ S) :
    IsIso (relativeChainProjection ℚ (neighborhoodSupportComplementPair W S)) :=
  isIso_relativeChainProjection _ ⟨fun w => w.2 (hWS w.1.2)⟩

/-- In normal dimension `0`, the full-support coclass is the constant class. -/
theorem fullSupportCoclass_zero_eq_augmentationClass {M : Type} [TopologicalSpace M]
    (W S : Set M) (hWS : W ⊆ S) :
    fullSupportCoclass 0 W S hWS =
      @augmentationClass _ (isIso_relativeChainProjection_of_subset W S hWS) := by
  have := isIso_relativeChainProjection_of_subset W S hWS
  rw [fullSupportCoclass, normalizedPointCoclass_zero]
  exact relativeCohomologyMap_augmentationClass _

end Point

end HodgeLean.RealDefs

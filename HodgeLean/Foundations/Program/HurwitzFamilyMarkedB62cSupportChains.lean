import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cMayerVietoris
import HodgeLean.RealDefs.ComplexFundamentalClassChainDefs

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular HodgeLean.RealDefs

variable (R : Type) [CommRing R] (M : Type) [TopologicalSpace M] (A B : Set M)

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeSumChainArrow : Arrow (ChainCategory R) :=
  Arrow.mk (b6m_twoSubsetSmallChainInclusion R (TopCat.of M) Aᶜ Bᶜ)

set_option backward.isDefEq.respectTransparency false in
def b6m_RelativeSumChainComplex : ChainCategory R :=
  (Limits.coker (C := ChainCategory R)).obj (b6m_relativeSumChainArrow R M A B)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_subsetLeftToSmallChains_comp_inclusion :
    SSet.chainComplexMap (subsetLeftToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ) (ModuleCat.of R R) ≫
        b6m_twoSubsetSmallChainInclusion R (TopCat.of M) Aᶜ Bᶜ =
      ((chainPairFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) Aᶜ)).hom := by
  let F := (SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)
  calc _ = F.map (subsetLeftToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ ≫
        (subsetSingularSubcomplex (TopCat.of M) Aᶜ ⊔
          subsetSingularSubcomplex (TopCat.of M) Bᶜ).ι) :=
          (F.map_comp _ _).symm
    _ = F.map (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of M) Aᶜ)) := rfl
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
lemma b6m_subsetRightToSmallChains_comp_inclusion :
    SSet.chainComplexMap (subsetRightToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ) (ModuleCat.of R R) ≫
        b6m_twoSubsetSmallChainInclusion R (TopCat.of M) Aᶜ Bᶜ =
      ((chainPairFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) Bᶜ)).hom := by
  let F := (SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)
  calc _ = F.map (subsetRightToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ ≫
        (subsetSingularSubcomplex (TopCat.of M) Aᶜ ⊔
          subsetSingularSubcomplex (TopCat.of M) Bᶜ).ι) :=
          (F.map_comp _ _).symm
    _ = F.map (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of M) Bᶜ)) := rfl
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeSumLeftArrowHom :
    (chainPairFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) Aᶜ) ⟶
      b6m_relativeSumChainArrow R M A B :=
  Arrow.homMk
    (SSet.chainComplexMap (subsetLeftToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ)
      (ModuleCat.of R R))
    (𝟙 _) ((b6m_subsetLeftToSmallChains_comp_inclusion R M A B).trans (Category.comp_id _).symm)

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeSumRightArrowHom :
    (chainPairFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) Bᶜ) ⟶
      b6m_relativeSumChainArrow R M A B :=
  Arrow.homMk
    (SSet.chainComplexMap (subsetRightToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ)
      (ModuleCat.of R R))
    (𝟙 _) ((b6m_subsetRightToSmallChains_comp_inclusion R M A B).trans (Category.comp_id _).symm)

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeSumLeftProjection :
    (relativeChainFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) Aᶜ) ⟶
      b6m_RelativeSumChainComplex R M A B :=
  (Limits.coker (C := ChainCategory R)).map (b6m_relativeSumLeftArrowHom R M A B)

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeSumRightProjection :
    (relativeChainFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) Bᶜ) ⟶
      b6m_RelativeSumChainComplex R M A B :=
  (Limits.coker (C := ChainCategory R)).map (b6m_relativeSumRightArrowHom R M A B)

set_option backward.isDefEq.respectTransparency false in
instance b6m_relativeChainProjection_epi (P : TopPair) : Epi (relativeChainProjection R P) := by
  change Epi (colimit.ι (parallelPair ((chainPairFunctor R).obj P).hom 0)
    WalkingParallelPair.one)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma b6m_relativeChainProjection_comp_supportInclusion {Z W : Set M} (h : Z ⊆ W) :
    relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Wᶜ) ≫
        (relativeChainFunctor R).map (supportInclusionPairMap (TopCat.of M) h) =
      relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Zᶜ) := by
  refine ((coker.π (C := ChainCategory R)).naturality
    ((chainPairFunctor R).map (supportInclusionPairMap (TopCat.of M) h))).symm.trans ?_
  have hid : Arrow.rightFunc.map
      ((chainPairFunctor R).map (supportInclusionPairMap (TopCat.of M) h)) = 𝟙 _ := by
    change ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
      (TopCat.toSSet.map (𝟙 _)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma b6m_relativeChainProjection_comp_relativeSumLeftProjection :
    relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) ≫
        b6m_relativeSumLeftProjection R M A B =
      (coker.π (C := ChainCategory R)).app (b6m_relativeSumChainArrow R M A B) :=
  ((coker.π (C := ChainCategory R)).naturality (b6m_relativeSumLeftArrowHom R M A B)).symm.trans
    (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_relativeChainProjection_comp_relativeSumRightProjection :
    relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Bᶜ) ≫
        b6m_relativeSumRightProjection R M A B =
      (coker.π (C := ChainCategory R)).app (b6m_relativeSumChainArrow R M A B) :=
  ((coker.π (C := ChainCategory R)).naturality (b6m_relativeSumRightArrowHom R M A B)).symm.trans
    (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeMayerVietorisShortComplex : ShortComplex (ChainCategory R) where
  X₁ := (relativeChainFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ)
  X₂ := (relativeChainFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) Aᶜ) ⊞
    (relativeChainFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) Bᶜ)
  X₃ := b6m_RelativeSumChainComplex R M A B
  f := biprod.lift
    ((relativeChainFunctor R).map
      (supportInclusionPairMap (TopCat.of M) (show A ⊆ A ∪ B from Set.subset_union_left)))
    (-(relativeChainFunctor R).map
      (supportInclusionPairMap (TopCat.of M) (show B ⊆ A ∪ B from Set.subset_union_right)))
  g := biprod.desc (b6m_relativeSumLeftProjection R M A B) (b6m_relativeSumRightProjection R M A B)
  zero := by
    apply (cancel_epi
      (relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ))).1
    rw [comp_zero, biprod.lift_desc, Preadditive.comp_add, Preadditive.neg_comp,
      Preadditive.comp_neg, ← Category.assoc, ← Category.assoc,
      b6m_relativeChainProjection_comp_supportInclusion R,
      b6m_relativeChainProjection_comp_supportInclusion R,
      b6m_relativeChainProjection_comp_relativeSumLeftProjection R,
      b6m_relativeChainProjection_comp_relativeSumRightProjection R, add_neg_cancel]

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeSumSmallChainComparison :
    (b6m_relativeSumChainArrow R M A B).left ⟶
      ((chainPairFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ)).left :=
  SSet.chainComplexMap
    (SSet.Subcomplex.homOfLE (relativeSumSubcomplex_le M A B) ≫
      (subsetSingularIso (TopCat.of M) (A ∩ B)ᶜ).inv)
    (ModuleCat.of R R)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_relativeSumSmallChainComparison_comp :
    b6m_relativeSumSmallChainComparison R M A B ≫
        ((chainPairFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ)).hom =
      b6m_twoSubsetSmallChainInclusion R (TopCat.of M) Aᶜ Bᶜ := by
  let F := (SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)
  have h : (subsetSingularIso (TopCat.of M) (A ∩ B)ᶜ).inv ≫
      TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of M) (A ∩ B)ᶜ) =
        (subsetSingularSubcomplex (TopCat.of M) (A ∩ B)ᶜ).ι := by
    rw [Iso.inv_comp_eq]; rfl
  calc _ = F.map ((SSet.Subcomplex.homOfLE (relativeSumSubcomplex_le M A B) ≫
        (subsetSingularIso (TopCat.of M) (A ∩ B)ᶜ).inv) ≫
          TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of M) (A ∩ B)ᶜ)) :=
          (F.map_comp _ _).symm
    _ = F.map (subsetSingularSubcomplex (TopCat.of M) Aᶜ ⊔
          subsetSingularSubcomplex (TopCat.of M) Bᶜ).ι := by
      rw [Category.assoc, h, SSet.Subcomplex.homOfLE_ι]
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeSumComparisonArrowHom :
    b6m_relativeSumChainArrow R M A B ⟶
      (chainPairFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ) :=
  Arrow.homMk (b6m_relativeSumSmallChainComparison R M A B) (𝟙 _)
    ((b6m_relativeSumSmallChainComparison_comp R M A B).trans (Category.comp_id _).symm)

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeSumComparison :
    b6m_RelativeSumChainComplex R M A B ⟶
      (relativeChainFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ) :=
  (Limits.coker (C := ChainCategory R)).map (b6m_relativeSumComparisonArrowHom R M A B)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_relativeSumLeftProjection_comp_comparison :
    b6m_relativeSumLeftProjection R M A B ≫ b6m_relativeSumComparison R M A B =
      (relativeChainFunctor R).map
        (supportInclusionPairMap (TopCat.of M) (show A ∩ B ⊆ A from Set.inter_subset_left)) := by
  apply (cancel_epi (relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Aᶜ))).1
  rw [← Category.assoc, b6m_relativeChainProjection_comp_relativeSumLeftProjection R,
    b6m_relativeChainProjection_comp_supportInclusion R]
  exact ((coker.π (C := ChainCategory R)).naturality
    (b6m_relativeSumComparisonArrowHom R M A B)).symm.trans (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_relativeSumRightProjection_comp_comparison :
    b6m_relativeSumRightProjection R M A B ≫ b6m_relativeSumComparison R M A B =
      (relativeChainFunctor R).map
        (supportInclusionPairMap (TopCat.of M) (show A ∩ B ⊆ B from Set.inter_subset_right)) := by
  apply (cancel_epi (relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Bᶜ))).1
  rw [← Category.assoc, b6m_relativeChainProjection_comp_relativeSumRightProjection R,
    b6m_relativeChainProjection_comp_supportInclusion R]
  exact ((coker.π (C := ChainCategory R)).naturality
    (b6m_relativeSumComparisonArrowHom R M A B)).symm.trans (Category.id_comp _)

end HodgeLean.Foundations.Program

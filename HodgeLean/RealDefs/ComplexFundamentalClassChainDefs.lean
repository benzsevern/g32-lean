import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.MayerVietoris
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

/-! # Chain complexes for the relative Mayer–Vietoris sequence

For subsets `A`, `B` of a space `M`, Hatcher's relative Mayer–Vietoris sequence comes from the
short exact sequence of rational singular chain complexes

`C(M)/C(M \ (A ∪ B)) → C(M)/C(M \ A) ⊕ C(M)/C(M \ B) → C(M)/(C(M \ A) + C(M \ B))`,

with maps `(r_A, -r_B)` and the sum of the two quotient maps. Here `C(M \ A) + C(M \ B)` is the
ported two-subset small-chain complex, with its inclusion `twoSubsetSmallChainInclusion` into
`C(M)`. This file names the last quotient, the two quotient maps into it, its comparison with
`C(M)/C(M \ (A ∩ B))`, and the short complex. Every map is induced by inclusions of singular
simplices; no choice is made and no hypothesis is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

variable (M : Type) [TopologicalSpace M] (A B : Set M)

/-- The inclusion `C(M \ A) + C(M \ B) → C(M)` of rational singular chains, as an arrow.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 149 (the chain complex `C_n(A + B)`). -/
def relativeSumChainArrow : Arrow (ChainCategory ℚ) :=
  Arrow.mk (twoSubsetSmallChainInclusion (TopCat.of M) Aᶜ Bᶜ)

example : (relativeSumChainArrow M A B).hom =
    twoSubsetSmallChainInclusion (TopCat.of M) Aᶜ Bᶜ :=
  rfl

/-- The quotient complex `C(M)/(C(M \ A) + C(M \ B))` of rational singular chains.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 152 (relative Mayer–Vietoris sequence). -/
def RelativeSumChainComplex : ChainCategory ℚ :=
  (Limits.coker (C := ChainCategory ℚ)).obj (relativeSumChainArrow M A B)

example : RelativeSumChainComplex M A B =
    (Limits.coker (C := ChainCategory ℚ)).obj
      (Arrow.mk (twoSubsetSmallChainInclusion (TopCat.of M) Aᶜ Bᶜ)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma subsetLeftToSmallChains_comp_inclusion :
    SSet.chainComplexMap (subsetLeftToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ) (ModuleCat.of ℚ ℚ) ≫
        twoSubsetSmallChainInclusion (TopCat.of M) Aᶜ Bᶜ =
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) Aᶜ)).hom := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  calc _ = F.map (subsetLeftToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ ≫
        (subsetSingularSubcomplex (TopCat.of M) Aᶜ ⊔
          subsetSingularSubcomplex (TopCat.of M) Bᶜ).ι) :=
          (F.map_comp _ _).symm
    _ = F.map (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of M) Aᶜ)) := rfl
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
lemma subsetRightToSmallChains_comp_inclusion :
    SSet.chainComplexMap (subsetRightToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ) (ModuleCat.of ℚ ℚ) ≫
        twoSubsetSmallChainInclusion (TopCat.of M) Aᶜ Bᶜ =
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) Bᶜ)).hom := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  calc _ = F.map (subsetRightToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ ≫
        (subsetSingularSubcomplex (TopCat.of M) Aᶜ ⊔
          subsetSingularSubcomplex (TopCat.of M) Bᶜ).ι) :=
          (F.map_comp _ _).symm
    _ = F.map (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of M) Bᶜ)) := rfl
    _ = _ := rfl

/-- `C(M \ A) → C(M \ A) + C(M \ B)` over the identity of `C(M)`, as a map of arrows.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 152. -/
def relativeSumLeftArrowHom :
    (chainPairFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) Aᶜ) ⟶
      relativeSumChainArrow M A B :=
  Arrow.homMk
    (SSet.chainComplexMap (subsetLeftToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ)
      (ModuleCat.of ℚ ℚ))
    (𝟙 _) ((subsetLeftToSmallChains_comp_inclusion M A B).trans (Category.comp_id _).symm)

example : (relativeSumLeftArrowHom M A B).right = 𝟙 _ :=
  rfl

/-- `C(M \ B) → C(M \ A) + C(M \ B)` over the identity of `C(M)`, as a map of arrows.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 152. -/
def relativeSumRightArrowHom :
    (chainPairFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) Bᶜ) ⟶
      relativeSumChainArrow M A B :=
  Arrow.homMk
    (SSet.chainComplexMap (subsetRightToSmallSingularSet (TopCat.of M) Aᶜ Bᶜ)
      (ModuleCat.of ℚ ℚ))
    (𝟙 _) ((subsetRightToSmallChains_comp_inclusion M A B).trans (Category.comp_id _).symm)

example : (relativeSumRightArrowHom M A B).right = 𝟙 _ :=
  rfl

/-- The quotient map `C(M)/C(M \ A) → C(M)/(C(M \ A) + C(M \ B))`.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 152. -/
def relativeSumLeftProjection :
    (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) Aᶜ) ⟶
      RelativeSumChainComplex M A B :=
  (Limits.coker (C := ChainCategory ℚ)).map (relativeSumLeftArrowHom M A B)

example : relativeSumLeftProjection M A B =
    (Limits.coker (C := ChainCategory ℚ)).map (relativeSumLeftArrowHom M A B) :=
  rfl

/-- The quotient map `C(M)/C(M \ B) → C(M)/(C(M \ A) + C(M \ B))`.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 152. -/
def relativeSumRightProjection :
    (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) Bᶜ) ⟶
      RelativeSumChainComplex M A B :=
  (Limits.coker (C := ChainCategory ℚ)).map (relativeSumRightArrowHom M A B)

example : relativeSumRightProjection M A B =
    (Limits.coker (C := ChainCategory ℚ)).map (relativeSumRightArrowHom M A B) :=
  rfl

/-- The projection from absolute to relative chains is an epimorphism. -/
instance relativeChainProjection_epi (P : TopPair) : Epi (relativeChainProjection ℚ P) := by
  change Epi (colimit.ι (parallelPair ((chainPairFunctor ℚ).obj P).hom 0)
    WalkingParallelPair.one)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of supports commutes with the projections from absolute chains. -/
lemma relativeChainProjection_comp_supportInclusion {Z W : Set M} (h : Z ⊆ W) :
    relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Wᶜ) ≫
        (relativeChainFunctor ℚ).map (supportInclusionPairMap (TopCat.of M) h) =
      relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Zᶜ) := by
  refine ((coker.π (C := ChainCategory ℚ)).naturality
    ((chainPairFunctor ℚ).map (supportInclusionPairMap (TopCat.of M) h))).symm.trans ?_
  have hid : Arrow.rightFunc.map
      ((chainPairFunctor ℚ).map (supportInclusionPairMap (TopCat.of M) h)) = 𝟙 _ := by
    change ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map
      (TopCat.toSSet.map (𝟙 _)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma relativeChainProjection_comp_relativeSumLeftProjection :
    relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ) ≫
        relativeSumLeftProjection M A B =
      (coker.π (C := ChainCategory ℚ)).app (relativeSumChainArrow M A B) :=
  ((coker.π (C := ChainCategory ℚ)).naturality (relativeSumLeftArrowHom M A B)).symm.trans
    (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
lemma relativeChainProjection_comp_relativeSumRightProjection :
    relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Bᶜ) ≫
        relativeSumRightProjection M A B =
      (coker.π (C := ChainCategory ℚ)).app (relativeSumChainArrow M A B) :=
  ((coker.π (C := ChainCategory ℚ)).naturality (relativeSumRightArrowHom M A B)).symm.trans
    (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
/-- The relative Mayer–Vietoris sequence of chain complexes
`C(M)/C(M \ (A ∪ B)) → C(M)/C(M \ A) ⊞ C(M)/C(M \ B) → C(M)/(C(M \ A) + C(M \ B))`, with maps
`(r_A, -r_B)` and the sum of the two quotient maps.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 152 (relative Mayer–Vietoris sequence). -/
def relativeMayerVietorisShortComplex : ShortComplex (ChainCategory ℚ) where
  X₁ := (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ)
  X₂ := (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) Aᶜ) ⊞
    (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) Bᶜ)
  X₃ := RelativeSumChainComplex M A B
  f := biprod.lift
    ((relativeChainFunctor ℚ).map
      (supportInclusionPairMap (TopCat.of M) (show A ⊆ A ∪ B from Set.subset_union_left)))
    (-(relativeChainFunctor ℚ).map
      (supportInclusionPairMap (TopCat.of M) (show B ⊆ A ∪ B from Set.subset_union_right)))
  g := biprod.desc (relativeSumLeftProjection M A B) (relativeSumRightProjection M A B)
  zero := by
    apply (cancel_epi
      (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ))).1
    rw [comp_zero, biprod.lift_desc, Preadditive.comp_add, Preadditive.neg_comp,
      Preadditive.comp_neg, ← Category.assoc, ← Category.assoc,
      relativeChainProjection_comp_supportInclusion,
      relativeChainProjection_comp_supportInclusion,
      relativeChainProjection_comp_relativeSumLeftProjection,
      relativeChainProjection_comp_relativeSumRightProjection, add_neg_cancel]

example : (relativeMayerVietorisShortComplex M A B).X₃ = RelativeSumChainComplex M A B :=
  rfl

lemma relativeSumSubcomplex_le :
    subsetSingularSubcomplex (TopCat.of M) Aᶜ ⊔ subsetSingularSubcomplex (TopCat.of M) Bᶜ ≤
      subsetSingularSubcomplex (TopCat.of M) (A ∩ B)ᶜ := by
  have hmono : ∀ {W W' : Set M}, W ⊆ W' →
      subsetSingularSubcomplex (TopCat.of M) W ≤ subsetSingularSubcomplex (TopCat.of M) W' := by
    intro W W' h n s hs
    rw [mem_subsetSingularSubcomplex_iff] at hs ⊢
    exact fun t => h (hs t)
  exact sup_le (hmono fun x hx h => hx h.1) (hmono fun x hx h => hx h.2)

/-- The small-chain comparison `C(M \ A) + C(M \ B) → C(M \ (A ∩ B))`: the inclusion of the
chains small for the cover `{M \ A, M \ B}` of `M \ (A ∩ B)` into all singular chains of the
subspace `M \ (A ∩ B)`.
Source: Hatcher, *Algebraic Topology*, Proposition 2.21 (small chains), in the space
`M \ (A ∩ B)`. -/
def relativeSumSmallChainComparison :
    (relativeSumChainArrow M A B).left ⟶
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ)).left :=
  SSet.chainComplexMap
    (SSet.Subcomplex.homOfLE (relativeSumSubcomplex_le M A B) ≫
      (subsetSingularIso (TopCat.of M) (A ∩ B)ᶜ).inv)
    (ModuleCat.of ℚ ℚ)

example : relativeSumSmallChainComparison M A B =
    SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (relativeSumSubcomplex_le M A B) ≫
        (subsetSingularIso (TopCat.of M) (A ∩ B)ᶜ).inv)
      (ModuleCat.of ℚ ℚ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma relativeSumSmallChainComparison_comp :
    relativeSumSmallChainComparison M A B ≫
        ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ)).hom =
      twoSubsetSmallChainInclusion (TopCat.of M) Aᶜ Bᶜ := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
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

/-- The small-chain comparison over the identity of `C(M)`, as a map of arrows.
Source: Hatcher, *Algebraic Topology*, Proposition 2.21 and §2.2, p. 152. -/
def relativeSumComparisonArrowHom :
    relativeSumChainArrow M A B ⟶
      (chainPairFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ) :=
  Arrow.homMk (relativeSumSmallChainComparison M A B) (𝟙 _)
    ((relativeSumSmallChainComparison_comp M A B).trans (Category.comp_id _).symm)

example : (relativeSumComparisonArrowHom M A B).left = relativeSumSmallChainComparison M A B :=
  rfl

/-- The comparison `C(M)/(C(M \ A) + C(M \ B)) → C(M)/C(M \ (A ∩ B))`.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 152. -/
def relativeSumComparison :
    RelativeSumChainComplex M A B ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ) :=
  (Limits.coker (C := ChainCategory ℚ)).map (relativeSumComparisonArrowHom M A B)

example : relativeSumComparison M A B =
    (Limits.coker (C := ChainCategory ℚ)).map (relativeSumComparisonArrowHom M A B) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The left quotient map followed by the comparison is restriction from `A` to `A ∩ B`. -/
lemma relativeSumLeftProjection_comp_comparison :
    relativeSumLeftProjection M A B ≫ relativeSumComparison M A B =
      (relativeChainFunctor ℚ).map
        (supportInclusionPairMap (TopCat.of M) (show A ∩ B ⊆ A from Set.inter_subset_left)) := by
  apply (cancel_epi (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ))).1
  rw [← Category.assoc, relativeChainProjection_comp_relativeSumLeftProjection,
    relativeChainProjection_comp_supportInclusion]
  exact ((coker.π (C := ChainCategory ℚ)).naturality
    (relativeSumComparisonArrowHom M A B)).symm.trans (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
/-- The right quotient map followed by the comparison is restriction from `B` to `A ∩ B`. -/
lemma relativeSumRightProjection_comp_comparison :
    relativeSumRightProjection M A B ≫ relativeSumComparison M A B =
      (relativeChainFunctor ℚ).map
        (supportInclusionPairMap (TopCat.of M) (show A ∩ B ⊆ B from Set.inter_subset_right)) := by
  apply (cancel_epi (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Bᶜ))).1
  rw [← Category.assoc, relativeChainProjection_comp_relativeSumRightProjection,
    relativeChainProjection_comp_supportInclusion]
  exact ((coker.π (C := ChainCategory ℚ)).naturality
    (relativeSumComparisonArrowHom M A B)).symm.trans (Category.id_comp _)

end HodgeLean.RealDefs

end

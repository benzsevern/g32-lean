import HodgeLean.RealDefs.ComplexFundamentalClassChainDefs
import HodgeLean.RealDefs.ComplexFundamentalClassParts.A_ShortExact

/-! # Short exactness of the relative Mayer–Vietoris chain sequence

The sequence `C(M)/C(M \ (A ∪ B)) → C(M)/C(M \ A) ⊞ C(M)/C(M \ B) → C(M)/(C(M \ A) + C(M \ B))`
is the cokernel row of the map from the absolute small-chain Mayer–Vietoris sequence of the
subsets `M \ A`, `M \ B` to the split sequence `C(M) → C(M) ⊞ C(M) → C(M)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

/-- The split short complex `X → X ⊞ X → X` with maps `(𝟙, -𝟙)` and `𝟙 + 𝟙`.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 149 (the sequence `0 → C(A ∩ B) → C(A) ⊕ C(B)
→ C(A + B) → 0` for `A = B = X`). -/
def diagonalDifferenceShortComplex (X : ChainCategory ℚ) : ShortComplex (ChainCategory ℚ) :=
  ShortComplex.mk (biprod.lift (𝟙 X) (-𝟙 X)) (biprod.desc (𝟙 X) (𝟙 X)) (by simp)

example (X : ChainCategory ℚ) : (diagonalDifferenceShortComplex X).g = biprod.desc (𝟙 X) (𝟙 X) :=
  rfl

lemma diagonalDifferenceShortComplex_shortExact (X : ChainCategory ℚ) :
    (diagonalDifferenceShortComplex X).ShortExact := by
  have hid : (biprod.fst ≫ biprod.lift (𝟙 X) (-𝟙 X) + biprod.desc (𝟙 X) (𝟙 X) ≫ biprod.inr :
      X ⊞ X ⟶ X ⊞ X) = 𝟙 _ := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
  exact ShortComplex.Splitting.shortExact
    { r := biprod.fst
      s := biprod.inr
      f_r := by simp [diagonalDifferenceShortComplex]
      s_g := by simp [diagonalDifferenceShortComplex]
      id := hid }

variable (M : Type) [TopologicalSpace M] (A B : Set M)

private abbrev G : TopCat ⥤ ChainCategory ℚ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)

/-- The identity of points from the subspace `Aᶜ ∩ Bᶜ` to the subspace `(A ∪ B)ᶜ`.
Source: De Morgan's law `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ` (Mathlib `Set.compl_union`). -/
def interComplToUnionCompl : TopCat.of ↥(Aᶜ ∩ Bᶜ) ⟶ TopCat.of ↥((A ∪ B)ᶜ) :=
  TopCat.ofHom ⟨fun x => ⟨x.1, fun h => h.elim x.2.1 x.2.2⟩, by fun_prop⟩

example (x : ↥(Aᶜ ∩ Bᶜ)) : (interComplToUnionCompl M A B x).1 = x.1 :=
  rfl

/-- The identity of points from the subspace `(A ∪ B)ᶜ` to the subspace `Aᶜ ∩ Bᶜ`.
Source: De Morgan's law `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ` (Mathlib `Set.compl_union`). -/
def unionComplToInterCompl : TopCat.of ↥((A ∪ B)ᶜ) ⟶ TopCat.of ↥(Aᶜ ∩ Bᶜ) :=
  TopCat.ofHom ⟨fun x => ⟨x.1, fun h => x.2 (Or.inl h), fun h => x.2 (Or.inr h)⟩, by fun_prop⟩

example (x : ↥((A ∪ B)ᶜ)) : (unionComplToInterCompl M A B x).1 = x.1 :=
  rfl

instance : IsIso (interComplToUnionCompl M A B) :=
  ⟨unionComplToInterCompl M A B, by ext; rfl, by ext; rfl⟩

lemma chainPairHom_eq (U : Set M) :
    ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of M) U)).hom =
      G.map (topologicalSubsetInclusion (TopCat.of M) U) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The absolute small-chain Mayer–Vietoris sequence of `M \ A`, `M \ B` maps to the split
sequence of `C(M)` by inclusions.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 152 (the relative Mayer–Vietoris sequence as a
quotient of absolute ones). -/
def relativeMayerVietorisAbsoluteHom :
    singularMayerVietorisShortComplex (TopCat.of M) Aᶜ Bᶜ ⟶
      diagonalDifferenceShortComplex (G.obj (TopCat.of M)) where
  τ₁ := G.map (topologicalSubsetInclusion (TopCat.of M) (Aᶜ ∩ Bᶜ))
  τ₂ := biprod.map (G.map (topologicalSubsetInclusion (TopCat.of M) Aᶜ))
    (G.map (topologicalSubsetInclusion (TopCat.of M) Bᶜ))
  τ₃ := twoSubsetSmallChainInclusion (TopCat.of M) Aᶜ Bᶜ
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [diagonalDifferenceShortComplex, singularMayerVietorisShortComplex,
        CommSq.shortComplex_f, Category.assoc, biprod.lift_fst, Category.comp_id, biprod.map_fst,
        biprod.lift_fst_assoc]
      exact (G.map_comp (subsetIntersectionToLeft (TopCat.of M) Aᶜ Bᶜ)
        (topologicalSubsetInclusion (TopCat.of M) Aᶜ))
    · simp only [diagonalDifferenceShortComplex, singularMayerVietorisShortComplex,
        CommSq.shortComplex_f, Category.assoc, biprod.lift_snd, Preadditive.comp_neg,
        Category.comp_id, biprod.map_snd, biprod.lift_snd_assoc, Preadditive.neg_comp]
      exact congrArg Neg.neg (G.map_comp (subsetIntersectionToRight (TopCat.of M) Aᶜ Bᶜ)
        (topologicalSubsetInclusion (TopCat.of M) Bᶜ))
  comm₂₃ := by
    have h := singularMayerVietorisSumChainMap_eq (TopCat.of M) Aᶜ Bᶜ
    rw [singularMayerVietorisSumChainMap] at h
    refine Eq.trans ?_ h.symm
    apply biprod.hom_ext' <;> simp [diagonalDifferenceShortComplex] <;> rfl

example : (relativeMayerVietorisAbsoluteHom M A B).τ₃ =
    twoSubsetSmallChainInclusion (TopCat.of M) Aᶜ Bᶜ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The split sequence of `C(M)` maps to the relative Mayer–Vietoris sequence by the quotient
maps.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 152 (the relative Mayer–Vietoris sequence as a
quotient of absolute ones). -/
def relativeMayerVietorisProjectionHom :
    diagonalDifferenceShortComplex (G.obj (TopCat.of M)) ⟶
      relativeMayerVietorisShortComplex M A B where
  τ₁ := relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ)
  τ₂ := biprod.map (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ))
    (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Bᶜ))
  τ₃ := (coker.π (C := ChainCategory ℚ)).app (relativeSumChainArrow M A B)
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [diagonalDifferenceShortComplex, relativeMayerVietorisShortComplex,
        Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc,
        Category.id_comp]
      exact relativeChainProjection_comp_supportInclusion M _
    · simp only [diagonalDifferenceShortComplex, relativeMayerVietorisShortComplex,
        Category.assoc, biprod.lift_snd, Preadditive.comp_neg, biprod.map_snd,
        biprod.lift_snd_assoc, Preadditive.neg_comp, Category.id_comp]
      exact congrArg Neg.neg (relativeChainProjection_comp_supportInclusion M _)
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [diagonalDifferenceShortComplex, relativeMayerVietorisShortComplex,
        biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc, Category.id_comp]
      exact relativeChainProjection_comp_relativeSumLeftProjection M A B
    · simp only [diagonalDifferenceShortComplex, relativeMayerVietorisShortComplex,
        biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc, Category.id_comp]
      exact relativeChainProjection_comp_relativeSumRightProjection M A B

example : (relativeMayerVietorisProjectionHom M A B).τ₁ =
    relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma relativeMayerVietorisAbsoluteHom_comp_projectionHom :
    relativeMayerVietorisAbsoluteHom M A B ≫ relativeMayerVietorisProjectionHom M A B = 0 := by
  ext : 1
  · change G.map (interComplToUnionCompl M A B ≫
        topologicalSubsetInclusion (TopCat.of M) (A ∪ B)ᶜ) ≫
          relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) = 0
    rw [G.map_comp, Category.assoc]
    erw [cokernel.condition]
    rw [comp_zero]
  · have hA : G.map (topologicalSubsetInclusion (TopCat.of M) Aᶜ) ≫
        relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ) = 0 :=
      cokernel.condition _
    have hB : G.map (topologicalSubsetInclusion (TopCat.of M) Bᶜ) ≫
        relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Bᶜ) = 0 :=
      cokernel.condition _
    change biprod.map (G.map (topologicalSubsetInclusion (TopCat.of M) Aᶜ))
        (G.map (topologicalSubsetInclusion (TopCat.of M) Bᶜ)) ≫
      biprod.map (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ))
        (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of M) Bᶜ)) = 0
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.map_fst, biprod.map_fst_assoc, hA, comp_zero, zero_comp]
    · rw [Category.assoc, biprod.map_snd, biprod.map_snd_assoc, hB, comp_zero, zero_comp]
  · exact cokernel.condition _

/-- The cokernel sequence `C(M \ A) + C(M \ B) → C(M) → C(M)/(C(M \ A) + C(M \ B))`.
Source: Hatcher, *Algebraic Topology*, §2.1, p. 115 (the short exact sequence of a pair of chain
complexes), for the subcomplex `C(M \ A) + C(M \ B)` of Hatcher §2.2, p. 149. -/
def relativeSumCokernelSequence : ShortComplex (ChainCategory ℚ) :=
  ShortComplex.mk (relativeSumChainArrow M A B).hom
    ((coker.π (C := ChainCategory ℚ)).app (relativeSumChainArrow M A B))
    (cokernel.condition _)

example : (relativeSumCokernelSequence M A B).X₃ = RelativeSumChainComplex M A B :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma relativeSumCokernelSequence_shortExact : (relativeSumCokernelSequence M A B).ShortExact := by
  have : Mono (twoSubsetSmallChainInclusion (TopCat.of M) Aᶜ Bᶜ) := by
    dsimp [twoSubsetSmallChainInclusion, SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  exact
    { exact := ShortComplex.exact_cokernel (twoSubsetSmallChainInclusion (TopCat.of M) Aᶜ Bᶜ)
      mono_f := this
      epi_g := coequalizer.π_epi }

set_option backward.isDefEq.respectTransparency false in
/-- The relative Mayer–Vietoris sequence of chain complexes is short exact. -/
theorem relativeMayerVietorisShortComplex_shortExact :
    (relativeMayerVietorisShortComplex M A B).ShortExact := by
  refine shortExact_of_shortExact_columns (relativeMayerVietorisAbsoluteHom M A B)
    (relativeMayerVietorisProjectionHom M A B)
    (relativeMayerVietorisAbsoluteHom_comp_projectionHom M A B)
    (singularMayerVietorisShortComplex_shortExact (TopCat.of M) Aᶜ Bᶜ)
    (diagonalDifferenceShortComplex_shortExact _) ?_ ?_ ?_
  · refine ShortComplex.shortExact_of_iso ?_
      (relativeChainShortComplex_shortExact ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ))
    refine ShortComplex.isoMk (G.mapIso (asIso (interComplToUnionCompl M A B))).symm
      (Iso.refl _) (Iso.refl _) ?_ (by simp; rfl)
    rw [Iso.symm_hom, Functor.mapIso_inv, asIso_inv, Iso.refl_hom, Category.comp_id,
      Functor.map_inv]
    change inv (G.map (interComplToUnionCompl M A B)) ≫
        G.map (topologicalSubsetInclusion (TopCat.of M) (Aᶜ ∩ Bᶜ)) =
      G.map (topologicalSubsetInclusion (TopCat.of M) (A ∪ B)ᶜ)
    rw [IsIso.inv_comp_eq, ← G.map_comp]
    rfl
  · exact biprod_shortExact
      (relativeChainShortComplex_shortExact ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ))
      (relativeChainShortComplex_shortExact ℚ (TopPair.ofSubset (X := TopCat.of M) Bᶜ))
  · exact relativeSumCokernelSequence_shortExact M A B

set_option backward.isDefEq.respectTransparency false in
/-- The comparison of the cokernel sequence of `C(M \ A) + C(M \ B)` with that of
`C(M \ (A ∩ B))`, over the identity of `C(M)`.
Source: Hatcher, *Algebraic Topology*, §2.2, p. 152 (the relative Mayer–Vietoris sequence for
closed sets uses `C(M \ A) + C(M \ B) → C(M \ (A ∩ B))`). -/
def relativeSumCokernelSequenceComparison :
    relativeSumCokernelSequence M A B ⟶
      relativeChainShortComplex ℚ (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ) where
  τ₁ := relativeSumSmallChainComparison M A B
  τ₂ := 𝟙 _
  τ₃ := relativeSumComparison M A B
  comm₁₂ := (relativeSumSmallChainComparison_comp M A B).trans (Category.comp_id _).symm
  comm₂₃ := (Category.id_comp _).trans
    (((coker.π (C := ChainCategory ℚ)).naturality
      (relativeSumComparisonArrowHom M A B)).symm.trans (Category.id_comp _)).symm

example : (relativeSumCokernelSequenceComparison M A B).τ₃ = relativeSumComparison M A B :=
  rfl

/-- If the small-chain comparison is a quasi-isomorphism, so is the comparison of quotients. -/
theorem relativeSumComparison_quasiIso_of_small
    (h : QuasiIso (relativeSumSmallChainComparison M A B)) :
    QuasiIso (relativeSumComparison M A B) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (relativeSumCokernelSequenceComparison M A B)
    (relativeSumCokernelSequence_shortExact M A B)
    (relativeChainShortComplex_shortExact ℚ _) h (quasiIso_of_isIso (𝟙 _))

end HodgeLean.RealDefs

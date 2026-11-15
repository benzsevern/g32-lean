import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSupportChains
import HodgeLean.RealDefs.ComplexFundamentalClassParts.A_RelativeMayerVietoris
import HodgeLean.RealDefs.ComplexFundamentalClassParts.A_SmallChains

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular HodgeLean.RealDefs
variable (R : Type) [CommRing R]

private abbrev G : TopCat ⥤ ChainCategory R :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)

variable (M : Type) [TopologicalSpace M] (A B : Set M)

set_option backward.isDefEq.respectTransparency false in
def b6m_diagonalDifferenceShortComplex (X : ChainCategory R) : ShortComplex (ChainCategory R) :=
  ShortComplex.mk (biprod.lift (𝟙 X) (-𝟙 X)) (biprod.desc (𝟙 X) (𝟙 X)) (by simp)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_diagonalDifferenceShortComplex_shortExact (X : ChainCategory R) :
    (b6m_diagonalDifferenceShortComplex R X).ShortExact := by
  have hid : (biprod.fst ≫ biprod.lift (𝟙 X) (-𝟙 X) + biprod.desc (𝟙 X) (𝟙 X) ≫ biprod.inr :
      X ⊞ X ⟶ X ⊞ X) = 𝟙 _ := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
  exact ShortComplex.Splitting.shortExact
    { r := biprod.fst
      s := biprod.inr
      f_r := by simp [b6m_diagonalDifferenceShortComplex]
      s_g := by simp [b6m_diagonalDifferenceShortComplex]
      id := hid }

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeMayerVietorisAbsoluteHom :
    b6m_singularMayerVietorisShortComplex R (TopCat.of M) Aᶜ Bᶜ ⟶
      b6m_diagonalDifferenceShortComplex R ((G R).obj (TopCat.of M)) where
  τ₁ := (G R).map (topologicalSubsetInclusion (TopCat.of M) (Aᶜ ∩ Bᶜ))
  τ₂ := biprod.map ((G R).map (topologicalSubsetInclusion (TopCat.of M) Aᶜ))
    ((G R).map (topologicalSubsetInclusion (TopCat.of M) Bᶜ))
  τ₃ := b6m_twoSubsetSmallChainInclusion R (TopCat.of M) Aᶜ Bᶜ
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [b6m_diagonalDifferenceShortComplex, b6m_singularMayerVietorisShortComplex,
        CommSq.shortComplex_f, Category.assoc, biprod.lift_fst, Category.comp_id, biprod.map_fst,
        biprod.lift_fst_assoc]
      exact ((G R).map_comp (subsetIntersectionToLeft (TopCat.of M) Aᶜ Bᶜ)
        (topologicalSubsetInclusion (TopCat.of M) Aᶜ))
    · simp only [b6m_diagonalDifferenceShortComplex, b6m_singularMayerVietorisShortComplex,
        CommSq.shortComplex_f, Category.assoc, biprod.lift_snd, Preadditive.comp_neg,
        Category.comp_id, biprod.map_snd, biprod.lift_snd_assoc, Preadditive.neg_comp]
      exact congrArg Neg.neg ((G R).map_comp (subsetIntersectionToRight (TopCat.of M) Aᶜ Bᶜ)
        (topologicalSubsetInclusion (TopCat.of M) Bᶜ))
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [b6m_diagonalDifferenceShortComplex, b6m_singularMayerVietorisShortComplex,
        CommSq.shortComplex_g, biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc,
        Category.comp_id]
      exact (b6m_subsetLeftToSmallChains_comp_inclusion R M A B).symm
    · simp only [b6m_diagonalDifferenceShortComplex, b6m_singularMayerVietorisShortComplex,
        CommSq.shortComplex_g, biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc,
        Category.comp_id]
      exact (b6m_subsetRightToSmallChains_comp_inclusion R M A B).symm

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeMayerVietorisProjectionHom :
    b6m_diagonalDifferenceShortComplex R ((G R).obj (TopCat.of M)) ⟶
      b6m_relativeMayerVietorisShortComplex R M A B where
  τ₁ := relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ)
  τ₂ := biprod.map (relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Aᶜ))
    (relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Bᶜ))
  τ₃ := (coker.π (C := ChainCategory R)).app (b6m_relativeSumChainArrow R M A B)
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [b6m_diagonalDifferenceShortComplex, b6m_relativeMayerVietorisShortComplex,
        Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc,
        Category.id_comp]
      exact b6m_relativeChainProjection_comp_supportInclusion R M _
    · simp only [b6m_diagonalDifferenceShortComplex, b6m_relativeMayerVietorisShortComplex,
        Category.assoc, biprod.lift_snd, Preadditive.comp_neg, biprod.map_snd,
        biprod.lift_snd_assoc, Preadditive.neg_comp, Category.id_comp]
      exact congrArg Neg.neg (b6m_relativeChainProjection_comp_supportInclusion R M _)
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [b6m_diagonalDifferenceShortComplex, b6m_relativeMayerVietorisShortComplex,
        biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc, Category.id_comp]
      exact b6m_relativeChainProjection_comp_relativeSumLeftProjection R M A B
    · simp only [b6m_diagonalDifferenceShortComplex, b6m_relativeMayerVietorisShortComplex,
        biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc, Category.id_comp]
      exact b6m_relativeChainProjection_comp_relativeSumRightProjection R M A B

set_option backward.isDefEq.respectTransparency false in
lemma b6m_relativeMayerVietorisAbsoluteHom_comp_projectionHom :
    b6m_relativeMayerVietorisAbsoluteHom R M A B ≫ b6m_relativeMayerVietorisProjectionHom R M A B = 0 := by
  ext : 1
  · change (G R).map (interComplToUnionCompl M A B ≫
        topologicalSubsetInclusion (TopCat.of M) (A ∪ B)ᶜ) ≫
          relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) = 0
    rw [(G R).map_comp, Category.assoc]
    erw [cokernel.condition]
    rw [comp_zero]
  · have hA : (G R).map (topologicalSubsetInclusion (TopCat.of M) Aᶜ) ≫
        relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) = 0 :=
      cokernel.condition _
    have hB : (G R).map (topologicalSubsetInclusion (TopCat.of M) Bᶜ) ≫
        relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Bᶜ) = 0 :=
      cokernel.condition _
    change biprod.map ((G R).map (topologicalSubsetInclusion (TopCat.of M) Aᶜ))
        ((G R).map (topologicalSubsetInclusion (TopCat.of M) Bᶜ)) ≫
      biprod.map (relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Aᶜ))
        (relativeChainProjection R (TopPair.ofSubset (X := TopCat.of M) Bᶜ)) = 0
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.map_fst, biprod.map_fst_assoc, hA, comp_zero, zero_comp]
    · rw [Category.assoc, biprod.map_snd, biprod.map_snd_assoc, hB, comp_zero, zero_comp]
  · exact cokernel.condition _

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeSumCokernelSequence : ShortComplex (ChainCategory R) :=
  ShortComplex.mk (b6m_relativeSumChainArrow R M A B).hom
    ((coker.π (C := ChainCategory R)).app (b6m_relativeSumChainArrow R M A B))
    (cokernel.condition _)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_relativeSumCokernelSequence_shortExact : (b6m_relativeSumCokernelSequence R M A B).ShortExact := by
  have : Mono (b6m_twoSubsetSmallChainInclusion R (TopCat.of M) Aᶜ Bᶜ) := by
    dsimp [b6m_twoSubsetSmallChainInclusion, SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  exact
    { exact := ShortComplex.exact_cokernel (b6m_twoSubsetSmallChainInclusion R (TopCat.of M) Aᶜ Bᶜ)
      mono_f := this
      epi_g := coequalizer.π_epi }

set_option backward.isDefEq.respectTransparency false in
theorem b6m_relativeMayerVietorisShortComplex_shortExact :
    (b6m_relativeMayerVietorisShortComplex R M A B).ShortExact := by
  refine shortExact_of_shortExact_columns (b6m_relativeMayerVietorisAbsoluteHom R M A B)
    (b6m_relativeMayerVietorisProjectionHom R M A B)
    (b6m_relativeMayerVietorisAbsoluteHom_comp_projectionHom R M A B)
    (b6m_singularMayerVietorisShortComplex_shortExact R (TopCat.of M) Aᶜ Bᶜ)
    (b6m_diagonalDifferenceShortComplex_shortExact R _) ?_ ?_ ?_
  · refine ShortComplex.shortExact_of_iso ?_
      (relativeChainShortComplex_shortExact R (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ))
    refine ShortComplex.isoMk ((G R).mapIso (asIso (interComplToUnionCompl M A B))).symm
      (Iso.refl _) (Iso.refl _) ?_ (by simp; rfl)
    rw [Iso.symm_hom, Functor.mapIso_inv, asIso_inv, Iso.refl_hom, Category.comp_id,
      Functor.map_inv]
    change inv ((G R).map (interComplToUnionCompl M A B)) ≫
        (G R).map (topologicalSubsetInclusion (TopCat.of M) (Aᶜ ∩ Bᶜ)) =
      (G R).map (topologicalSubsetInclusion (TopCat.of M) (A ∪ B)ᶜ)
    rw [IsIso.inv_comp_eq, ← (G R).map_comp]
    rfl
  · exact biprod_shortExact
      (relativeChainShortComplex_shortExact R (TopPair.ofSubset (X := TopCat.of M) Aᶜ))
      (relativeChainShortComplex_shortExact R (TopPair.ofSubset (X := TopCat.of M) Bᶜ))
  · exact b6m_relativeSumCokernelSequence_shortExact R M A B

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeSumCokernelSequenceComparison :
    b6m_relativeSumCokernelSequence R M A B ⟶
      relativeChainShortComplex R (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ) where
  τ₁ := b6m_relativeSumSmallChainComparison R M A B
  τ₂ := 𝟙 _
  τ₃ := b6m_relativeSumComparison R M A B
  comm₁₂ := (b6m_relativeSumSmallChainComparison_comp R M A B).trans (Category.comp_id _).symm
  comm₂₃ := (Category.id_comp _).trans
    (((coker.π (C := ChainCategory R)).naturality
      (b6m_relativeSumComparisonArrowHom R M A B)).symm.trans (Category.id_comp _)).symm

set_option backward.isDefEq.respectTransparency false in
theorem b6m_relativeSumComparison_quasiIso_of_small
    (h : QuasiIso (b6m_relativeSumSmallChainComparison R M A B)) :
    QuasiIso (b6m_relativeSumComparison R M A B) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (b6m_relativeSumCokernelSequenceComparison R M A B)
    (b6m_relativeSumCokernelSequence_shortExact R M A B)
    (relativeChainShortComplex_shortExact R _) h (quasiIso_of_isIso (𝟙 _))

set_option backward.isDefEq.respectTransparency false in
theorem b6m_relativeSumSmallChainComparison_quasiIso_of_isClosed
    (hA : IsClosed A) (hB : IsClosed B) :
    QuasiIso (b6m_relativeSumSmallChainComparison R M A B) := by
  let Y := TopCat.of ↥((A ∩ B)ᶜ)
  have hU : IsOpen (interComplLeftCover A B) :=
    hA.isOpen_compl.preimage continuous_subtype_val
  have hV : IsOpen (interComplRightCover A B) :=
    hB.isOpen_compl.preimage continuous_subtype_val
  have hUV : interComplLeftCover A B ∪ interComplRightCover A B = Set.univ :=
    Set.eq_univ_of_forall fun y => not_and_or.mp y.2
  have ha := b6m_twoSubsetSmallChainInclusion_quasiIso R Y
    (interComplLeftCover A B) (interComplRightCover A B) hU hV hUV
  let F := (SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)
  have hfac : F.map (interComplSmallIso A B).hom ≫ b6m_relativeSumSmallChainComparison R M A B =
      b6m_twoSubsetSmallChainInclusion R Y
        (interComplLeftCover A B) (interComplRightCover A B) := by
    change F.map _ ≫ F.map _ = F.map _
    rw [← F.map_comp, interComplSmallIso_hom_comp]
  have : QuasiIso (F.map (interComplSmallIso A B).hom) := quasiIso_of_isIso _
  rw [← hfac] at ha
  exact (quasiIso_iff_comp_left (hφ := this) _ _).1 ha

end HodgeLean.Foundations.Program

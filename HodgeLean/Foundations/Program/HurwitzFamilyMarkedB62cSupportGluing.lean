import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSupportHomology

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
variable (R : Type) [CommRing R]

theorem b6m_relativeSumComparison_quasiIso {M : Type} [TopologicalSpace M] {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B) :
    QuasiIso (b6m_relativeSumComparison R M A B) :=
  b6m_relativeSumComparison_quasiIso_of_small R M A B
    (b6m_relativeSumSmallChainComparison_quasiIso_of_isClosed R M A B hA hB)

theorem b6m_relativeMayerVietoris_exact_middle {M : Type} [TopologicalSpace M] (A B : Set M) (i : ℕ)
    (a : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) i)
    (b : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Bᶜ) i)
    (hab : (HomologicalComplex.homologyMap (b6m_relativeSumLeftProjection R M A B) i).hom a =
      (HomologicalComplex.homologyMap (b6m_relativeSumRightProjection R M A B) i).hom b) :
    ∃ c : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) i,
      relativeHomologyMap R i
          (supportInclusionPairMap (TopCat.of M) (show A ⊆ A ∪ B from Set.subset_union_left)) c =
        a ∧
      relativeHomologyMap R i
          (supportInclusionPairMap (TopCat.of M) (show B ⊆ A ∪ B from Set.subset_union_right)) c =
        b := by
  exact b6m_homology_exact_middle_of_shortExact R _ _ _ _ _
    (b6m_relativeMayerVietorisShortComplex_shortExact R M A B) i a b hab

theorem b6m_relativeMayerVietoris_exact_left {M : Type} [TopologicalSpace M] (A B : Set M) (i : ℕ)
    (hvan : Subsingleton ((b6m_RelativeSumChainComplex R M A B).homology (i + 1)))
    (c : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) i)
    (hcA : relativeHomologyMap R i
      (supportInclusionPairMap (TopCat.of M) (show A ⊆ A ∪ B from Set.subset_union_left)) c = 0)
    (hcB : relativeHomologyMap R i
      (supportInclusionPairMap (TopCat.of M) (show B ⊆ A ∪ B from Set.subset_union_right)) c = 0) :
    c = 0 := by
  exact b6m_homology_exact_left_of_shortExact R _ _ _ _ _
    (b6m_relativeMayerVietorisShortComplex_shortExact R M A B) i hvan c hcA hcB

theorem b6m_relativeMayerVietoris_glue {M : Type} [TopologicalSpace M] {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B) (i : ℕ)
    (a : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) i)
    (b : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Bᶜ) i)
    (hab : relativeHomologyMap R i
        (supportInclusionPairMap (TopCat.of M) (show A ∩ B ⊆ A from Set.inter_subset_left)) a =
      relativeHomologyMap R i
        (supportInclusionPairMap (TopCat.of M) (show A ∩ B ⊆ B from Set.inter_subset_right)) b) :
    ∃ c : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) i,
      relativeHomologyMap R i
          (supportInclusionPairMap (TopCat.of M) (show A ⊆ A ∪ B from Set.subset_union_left)) c =
        a ∧
      relativeHomologyMap R i
          (supportInclusionPairMap (TopCat.of M) (show B ⊆ A ∪ B from Set.subset_union_right)) c =
        b := by
  have := b6m_relativeSumComparison_quasiIso R hA hB
  exact b6m_relativeMayerVietoris_exact_middle R A B i a b
    (b6m_homologyMap_eq_of_comp_quasiIso R _ _ (b6m_relativeSumComparison R M A B) _ _
      (b6m_relativeSumLeftProjection_comp_comparison R M A B)
      (b6m_relativeSumRightProjection_comp_comparison R M A B) i a b hab)

theorem b6m_relativeMayerVietoris_injective {M : Type} [TopologicalSpace M] {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B) (i : ℕ)
    (hvan : Subsingleton
      (RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ) (i + 1)))
    (c : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) i)
    (hcA : relativeHomologyMap R i
      (supportInclusionPairMap (TopCat.of M) (show A ⊆ A ∪ B from Set.subset_union_left)) c = 0)
    (hcB : relativeHomologyMap R i
      (supportInclusionPairMap (TopCat.of M) (show B ⊆ A ∪ B from Set.subset_union_right)) c = 0) :
    c = 0 := by
  have := b6m_relativeSumComparison_quasiIso R hA hB
  exact b6m_relativeMayerVietoris_exact_left R A B i
    (b6m_homology_subsingleton_of_quasiIso R (b6m_relativeSumComparison R M A B) (i + 1) hvan) c hcA hcB

theorem b6m_glue_local_classes {M : Type} [TopologicalSpace M] (n : ℕ)
    {A B : Set M} (hA : IsClosed A) (hB : IsClosed B)
    (μ : ∀ x : M, RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) ({x}ᶜ : Set M)) n)
    (a : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) n)
    (b : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Bᶜ) n)
    (ha : ∀ (x : M) (hx : x ∈ A), relativeHomologyMap R n
      (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) a = μ x)
    (hb : ∀ (x : M) (hx : x ∈ B), relativeHomologyMap R n
      (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) b = μ x)
    (hd : ∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ) n,
      (∀ (x : M) (hx : x ∈ A ∩ B), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0) :
    ∃ c : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) n,
      ∀ (x : M) (hx : x ∈ A ∪ B), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) c = μ x := by
  obtain ⟨c, hcA, hcB⟩ := b6m_relativeMayerVietoris_glue R hA hB n a b
    (sub_eq_zero.1 (hd _ fun x hx => by
      rw [map_sub, b6m_relativeHomologyMap_supportInclusion_trans,
        b6m_relativeHomologyMap_supportInclusion_trans, sub_eq_zero]
      exact (ha x hx.1).trans (hb x hx.2).symm))
  refine ⟨c, fun x hx => ?_⟩
  rcases hx with hx | hx
  · rw [← ha x hx, ← hcA, b6m_relativeHomologyMap_supportInclusion_trans]
  · rw [← hb x hx, ← hcB, b6m_relativeHomologyMap_supportInclusion_trans]

end HodgeLean.Foundations.Program

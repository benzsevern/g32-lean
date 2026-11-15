import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cChartHomology

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular

theorem b6m_local_class_exists_on_compact
    (R : Type) [CommRing R] {M E : Type} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    (μ : ∀ x : M, RelativeHomology R (pointComplementPair x) n)
    (hμ : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      ∃ c : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (U : Set M)ᶜ) n,
        ∀ (y : M) (hy : y ∈ U), relativeHomologyMap R n
          (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy)) c = μ y)
    {A : Set M} (hA : IsCompact A) :
    ∃ c : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) n,
      ∀ (y : M) (hy : y ∈ A), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy)) c = μ y := by
  classical
  choose U hxU c hc using hμ
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun x : M => (U x : Set M))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  obtain ⟨K, hKc, hKU, hAK⟩ := hA.finite_compact_cover t (fun x : M => (U x : Set M))
    (fun x _ => (U x).isOpen) ht
  have key : ∀ s : Finset M,
      ∃ d : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (⋃ i ∈ s, K i)ᶜ) n,
        ∀ (y : M) (hy : y ∈ ⋃ i ∈ s, K i), relativeHomologyMap R n
          (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy)) d = μ y := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact ⟨0, fun x hx => by simp at hx⟩
    · intro a s _ ih
      rw [Finset.set_biUnion_insert]
      obtain ⟨b, hb⟩ := ih
      have hs : IsCompact (⋃ i ∈ s, K i) := s.isCompact_biUnion fun i _ => hKc i
      refine b6m_glue_local_classes R n (hKc a).isClosed hs.isClosed μ
        (relativeHomologyMap R n (supportInclusionPairMap (TopCat.of M) (hKU a)) (c a)) b
        ?_ hb (b6m_compact_manifold_local_homology R hn
          ((hKc a).inter_right hs.isClosed)).2
      intro y hy
      rw [b6m_relativeHomologyMap_supportInclusion_trans]
      exact hc a y (hKU a hy)
  rw [hAK]
  exact key t

theorem b6m_global_class_exists_of_local_classes
    (R : Type) [CommRing R] {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    (μ : ∀ x : M, RelativeHomology R (pointComplementPair x) n)
    (hμ : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      ∃ c : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (U : Set M)ᶜ) n,
        ∀ (y : M) (hy : y ∈ U), relativeHomologyMap R n
          (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy)) c = μ y) :
    ∃ w : RelativeHomology R (TopPair.ofSubset
        (((⊤ : Opens M) : Set M)ᶜ : Set (TopCat.of M))) n,
      ∀ y : M, relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M)
          (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w = μ y := by
  obtain ⟨α, hα⟩ := b6m_local_class_exists_on_compact R hn μ hμ
    (A := ((⊤ : Opens M) : Set M)) (by rw [Opens.coe_top]; exact isCompact_univ)
  exact ⟨α, fun y => hα y (Opens.mem_top y)⟩

end HodgeLean.Foundations.Program

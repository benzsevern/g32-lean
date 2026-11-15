import HodgeLean.Foundations.QuotientDuality.LocalHomologyNeighborhood
import HodgeLean.RealDefs.ComplexFundamentalClassProofs

/-! Compact-support detection from vanishing of the next relative singular group. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

/-- Vanishing one degree higher on compact supports gives detection by point values.
Source: Hatcher, Algebraic Topology, proof of Lemma 3.27. -/
theorem compact_detection_of_next_degree_vanishing (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (hv : ∀ B : Set X, IsCompact B →
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset (X := X) Bᶜ) (n + 1)))
    (A : Set X) (hA : IsCompact A) : LocalHomologyDetectedByPoints X n A := by
  classical
  intro α hα
  obtain ⟨W, hWo, hAW, hlift⟩ := C_exists_open_lift A n α
  obtain ⟨w, hw⟩ := hlift W hAW Set.Subset.rfl
  have hlocal (x : A) : relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr (hAW x.property))) w = 0 := by
    rw [← relativeHomologyMap_supportInclusion_trans
      (M := X) (Set.singleton_subset_iff.mpr x.property) hAW, hw]
    exact hα x.val x.property
  choose V hxV hVW hzero using fun x : A =>
    relative_class_zero_on_neighborhood X n ⟨W, hWo⟩ x.val (hAW x.property) w (hlocal x)
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun x : A => (V x : Set X))
    (fun x => (V x).isOpen) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  obtain ⟨K, hKc, hKV, hAK⟩ := hA.finite_compact_cover t (fun x : A => (V x : Set X))
    (fun x _ => (V x).isOpen) ht
  have hKW (x : A) : K x ⊆ W := (hKV x).trans (hVW x)
  have hBW (s : Finset A) : (⋃ i ∈ s, K i) ⊆ W := by
    simp only [Set.iUnion_subset_iff]
    exact fun i _ => hKW i
  have key : ∀ s : Finset A, relativeHomologyMap ℚ n
      (supportInclusionPairMap X (hBW s)) w = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have he := C_relativeHomology_compl_empty_isZero X n
      have hemp : (⋃ i ∈ (∅ : Finset A), K i) = ∅ := by simp
      have hsub : Subsingleton (RelativeHomology ℚ
          (TopPair.ofSubset (X := X) (⋃ i ∈ (∅ : Finset A), K i)ᶜ) n) := by
        simpa only [hemp] using ModuleCat.subsingleton_of_isZero he
      exact @Subsingleton.elim _ hsub _ _
    · intro a s ha ih
      let B := ⋃ i ∈ s, K i
      have hBc : IsCompact B := s.isCompact_biUnion fun i _ => hKc i
      have hUB : K a ∪ B ⊆ W := Set.union_subset (hKW a) (hBW s)
      have hz := j5c_relativeMayerVietoris_injective_aux (hKc a).isClosed hBc.isClosed n
        (hv _ ((hKc a).inter_right hBc.isClosed))
        (relativeHomologyMap ℚ n (supportInclusionPairMap X hUB) w)
      have hKa : relativeHomologyMap ℚ n
          (supportInclusionPairMap X (hKW a)) w = 0 := by
        calc
          _ = relativeHomologyMap ℚ n (supportInclusionPairMap X (hKV a))
              (relativeHomologyMap ℚ n (supportInclusionPairMap X (hVW a)) w) :=
            (relativeHomologyMap_supportInclusion_trans (hKV a) (hVW a) n w).symm
          _ = 0 := by rw [hzero a, map_zero]
      have hUzero : relativeHomologyMap ℚ n (supportInclusionPairMap X hUB) w = 0 := by
        apply hz
        · rw [relativeHomologyMap_supportInclusion_trans]
          exact hKa
        · rw [relativeHomologyMap_supportInclusion_trans]
          exact ih
      have hle : (⋃ i ∈ insert a s, K i) ⊆ K a ∪ B := by
        rw [Finset.set_biUnion_insert]
      have hz' := congrArg (relativeHomologyMap ℚ n (supportInclusionPairMap X hle)) hUzero
      rw [map_zero, relativeHomologyMap_supportInclusion_trans] at hz'
      exact hz'
  have htzero := key t
  have hAKsub : A ⊆ ⋃ i ∈ t, K i := hAK.le
  have hz := congrArg (relativeHomologyMap ℚ n (supportInclusionPairMap X hAKsub)) htzero
  rw [map_zero, relativeHomologyMap_supportInclusion_trans] at hz
  exact hw.symm.trans hz

/-- A uniform compact-support bound lets point-local vanishing descend to detection.
Source: Bredon, Sheaf Theory, V.9; the descent uses relative Mayer–Vietoris. -/
theorem compact_detection_of_uniform_bound (X : TopCat.{0}) [T2Space X] (n N : ℕ)
    (hl : ∀ (x : X) (i : ℕ), n < i → Subsingleton (RelativeHomology ℚ
      (pointComplementPair x) i))
    (hb : ∀ (A : Set X), IsCompact A → ∀ i : ℕ, N < i →
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset (X := X) Aᶜ) i))
    (A : Set X) (hA : IsCompact A) : LocalHomologyDetectedByPoints X n A := by
  induction N with
  | zero =>
    exact compact_detection_of_next_degree_vanishing X n
      (fun B hB => hb B hB (n + 1) (by omega)) A hA
  | succ N ih =>
    by_cases hn : N < n
    · exact compact_detection_of_next_degree_vanishing X n
        (fun B hB => hb B hB (n + 1) (by omega)) A hA
    · have htop (B : Set X) (hB : IsCompact B) :
          Subsingleton (RelativeHomology ℚ (TopPair.ofSubset (X := X) Bᶜ) (N + 1)) := by
        have hd := compact_detection_of_next_degree_vanishing X (N + 1)
          (fun D hD => hb D hD (N + 1 + 1) (by omega)) B hB
        have hz : ∀ c : RelativeHomology ℚ (TopPair.ofSubset (X := X) Bᶜ) (N + 1),
            c = 0 := by
          intro c
          apply hd
          intro x hx
          exact @Subsingleton.elim _ (hl x (N + 1) (by omega)) _ _
        exact ⟨fun c d => (hz c).trans (hz d).symm⟩
      apply ih
      intro B hB i hi
      by_cases he : i = N + 1
      · subst i
        exact htop B hB
      · exact hb B hB i (by omega)

#print axioms compact_detection_of_uniform_bound

#print axioms compact_detection_of_next_degree_vanishing
end HodgeLean.Foundations.QuotientDuality

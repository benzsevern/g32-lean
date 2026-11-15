import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cOpenLift
import HodgeLean.RealDefs.ComplexFundamentalClassParts.C_BallCover
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSupportGluing
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalHomologyCoefficients

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular

theorem b6m_union_local_homology
    (R : Type) [CommRing R] {M : Type} [TopologicalSpace M] (n : ℕ)
    {A B : Set M} (hA : IsClosed A) (hB : IsClosed B)
    (hvA : ∀ k, n < k → IsZero (RelativeHomology R
      (TopPair.ofSubset (X := TopCat.of M) Aᶜ) k))
    (hvB : ∀ k, n < k → IsZero (RelativeHomology R
      (TopPair.ofSubset (X := TopCat.of M) Bᶜ) k))
    (hvAB : ∀ k, n < k → IsZero (RelativeHomology R
      (TopPair.ofSubset (X := TopCat.of M) (A ∩ B)ᶜ) k))
    (hdA : ∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) n,
      (∀ (x : M) (hx : x ∈ A), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0)
    (hdB : ∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Bᶜ) n,
      (∀ (x : M) (hx : x ∈ B), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0) :
    (∀ k, n < k → IsZero (RelativeHomology R
      (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) k)) ∧
    (∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) n,
      (∀ (x : M) (hx : x ∈ A ∪ B), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0) := by
  refine ⟨fun k hk => ?_, fun c hc => ?_⟩
  · have := ModuleCat.subsingleton_of_isZero (hvA k hk)
    have := ModuleCat.subsingleton_of_isZero (hvB k hk)
    have hsub : ∀ e : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) k,
        e = 0 := fun e =>
      b6m_relativeMayerVietoris_injective R hA hB k
        (ModuleCat.subsingleton_of_isZero (hvAB (k + 1) (by omega))) e
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    have : Subsingleton (RelativeHomology R
        (TopPair.ofSubset (X := TopCat.of M) (A ∪ B)ᶜ) k) :=
      ⟨fun c d => (hsub c).trans (hsub d).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  · refine b6m_relativeMayerVietoris_injective R hA hB n
      (ModuleCat.subsingleton_of_isZero (hvAB (n + 1) (by omega))) c
      (hdA _ fun x hx => ?_) (hdB _ fun x hx => ?_)
    · rw [b6m_relativeHomologyMap_supportInclusion_trans]
      exact hc x (Or.inl hx)
    · rw [b6m_relativeHomologyMap_supportInclusion_trans]
      exact hc x (Or.inr hx)

theorem b6m_iUnion_convex_local_homology
    (R : Type) [CommRing R] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n) {m : ℕ} (K : Fin m → Set E)
    (hK : ∀ j, Convex ℝ (K j)) (hKc : ∀ j, IsCompact (K j)) :
    (∀ k, n < k → IsZero (RelativeHomology R
      (TopPair.ofSubset (X := TopCat.of E) (⋃ j, K j)ᶜ) k)) ∧
    (∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of E) (⋃ j, K j)ᶜ) n,
      (∀ (x : E) (hx : x ∈ ⋃ j, K j), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0) := by
  induction m with
  | zero =>
    rw [Set.iUnion_of_empty]
    exact b6m_convex_local_homology R hn (convex_empty (𝕜 := ℝ)) isCompact_empty
  | succ m ih =>
    have hU : (⋃ j, K j) = (⋃ j : Fin m, K j.castSucc) ∪ K (Fin.last m) := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨j, hj⟩
        induction j using Fin.lastCases with
        | last => exact Or.inr hj
        | cast j => exact Or.inl ⟨j, hj⟩
      · rintro (⟨j, hj⟩ | hj)
        · exact ⟨_, hj⟩
        · exact ⟨_, hj⟩
    rw [hU]
    have h1 := ih (fun j => K j.castSucc) (fun j => hK _) (fun j => hKc _)
    have h2 := b6m_convex_local_homology R hn (hK (Fin.last m)) (hKc _)
    have h3 := ih (fun j => K j.castSucc ∩ K (Fin.last m)) (fun j => (hK _).inter (hK _))
      (fun j => (hKc _).inter_right (hKc _).isClosed)
    rw [← Set.iUnion_inter] at h3
    exact b6m_union_local_homology R n (isCompact_iUnion fun j => hKc _).isClosed (hKc _).isClosed
      h1.1 h2.1 h3.1 h1.2 h2.2


theorem b6m_compact_euclidean_local_homology
    (R : Type) [CommRing R] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n) {A : Set E}
    (hA : IsCompact A) :
    (∀ k, n < k → IsZero (RelativeHomology R
      (TopPair.ofSubset (X := TopCat.of E) Aᶜ) k)) ∧
    (∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of E) Aᶜ) n,
      (∀ (x : E) (hx : x ∈ A), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0) := by
  have hlift : ∀ i (α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of E) Aᶜ) i),
      ∃ (m : ℕ) (c : Fin m → E) (δ : ℝ), 0 < δ ∧ (∀ j, c j ∈ A) ∧
        ∃ hAK : A ⊆ ⋃ j, Metric.closedBall (c j) δ,
          ∃ α' : RelativeHomology R (TopPair.ofSubset (X := TopCat.of E)
              (⋃ j, Metric.closedBall (c j) δ)ᶜ) i,
            relativeHomologyMap R i (supportInclusionPairMap (TopCat.of E) hAK) α' = α := by
    intro i α
    obtain ⟨W, hWo, hAW, hW⟩ := b6m_exists_open_lift R A i α
    obtain ⟨m, c, δ, hδ, hc, hAK, hKW⟩ := HodgeLean.RealDefs.C_exists_closedBall_cover hA hWo hAW
    exact ⟨m, c, δ, hδ, hc, hAK, hW _ hAK hKW⟩
  have hU := fun (m : ℕ) (c : Fin m → E) (δ : ℝ) =>
    b6m_iUnion_convex_local_homology R hn (fun j => Metric.closedBall (c j) δ)
      (fun j => convex_closedBall _ _) (fun j => isCompact_closedBall _ _)
  refine ⟨fun i hi => ?_, fun α hα => ?_⟩
  · suffices h : ∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of E) Aᶜ) i, α = 0 from
      by
        have : Subsingleton (RelativeHomology R (TopPair.ofSubset (X := TopCat.of E) Aᶜ) i) :=
          ⟨fun a b => (h a).trans (h b).symm⟩
        exact ModuleCat.isZero_of_subsingleton _
    intro α
    obtain ⟨m, c, δ, _, _, hAK, α', rfl⟩ := hlift i α
    have := ModuleCat.subsingleton_of_isZero ((hU m c δ).1 i hi)
    rw [Subsingleton.elim α' 0, map_zero]
  · obtain ⟨m, c, δ, hδ, hc, hAK, α', rfl⟩ := hlift n α
    suffices h : α' = 0 by rw [h, map_zero]
    refine (hU m c δ).2 α' fun y hy => ?_
    obtain ⟨j, hyB⟩ := Set.mem_iUnion.mp hy
    have hBK : Metric.closedBall (c j) δ ⊆ ⋃ j, Metric.closedBall (c j) δ :=
      Set.subset_iUnion (fun j => Metric.closedBall (c j) δ) j
    have hcB : c j ∈ Metric.closedBall (c j) δ := Metric.mem_closedBall_self hδ.le
    have hinj := (b6m_convex_restrict_bijective R (convex_closedBall (c j) δ)
      (isCompact_closedBall (c j) δ) hcB n).1
    have e2 := (b6m_relativeHomologyMap_supportInclusion_trans R (Set.singleton_subset_iff.mpr hcB) hBK n α').symm
    have e3 := (b6m_relativeHomologyMap_supportInclusion_trans R (Set.singleton_subset_iff.mpr (hc j)) hAK n α').symm
    have h0 : relativeHomologyMap R n (supportInclusionPairMap (TopCat.of E) hBK) α' = 0 := by
      apply hinj
      rw [map_zero]
      exact e2.symm.trans (e3.trans (hα (c j) (hc j)))
    have e1 := (b6m_relativeHomologyMap_supportInclusion_trans R (Set.singleton_subset_iff.mpr hyB) hBK n α').symm
    refine e1.trans ?_
    rw [h0, map_zero]


end HodgeLean.Foundations.Program

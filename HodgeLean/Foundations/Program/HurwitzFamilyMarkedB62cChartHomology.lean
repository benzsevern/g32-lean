import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cCompactSupport
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cExcision
import HodgeLean.RealDefs.ComplexFundamentalClassParts.E_Chart

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular HodgeLean.RealDefs
variable (R : Type) [CommRing R]

theorem b6m_relativeHomologyMap_iso_injective {P Q : TopPair} (φ : P ≅ Q) (i : ℕ) :
    Function.Injective (relativeHomologyMap R i φ.hom) := by
  have hiso : IsIso ((relativeHomologyFunctor R i).map φ.hom) := inferInstance
  exact ((ConcreteCategory.isIso_iff_bijective _).mp hiso).1

theorem b6m_local_homology_of_homeomorph {M E : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n)
    {U : Set M} (hU : IsOpen U) {V : Set E} (hV : IsOpen V) (h : U ≃ₜ V)
    {A : Set M} (hA : IsClosed A) (hAU : A ⊆ U) {A' : Set E} (hA'c : IsCompact A')
    (hA'V : A' ⊆ V) (hAA' : ∀ u : U, (h u : E) ∈ A' ↔ (u : M) ∈ A) :
    (∀ k, n < k → IsZero (RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) k)) ∧ (∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) n,
      (∀ (x : M) (hx : x ∈ A), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0) := by
  have hEuc := b6m_compact_euclidean_local_homology R hn hA'c
  have hexM : ∀ i, Function.Bijective (relativeHomologyMap R i (j5cE_exMap U A)) :=
    fun i => b6m_closed_support_excision_bijective R hU hA hAU i
  have hexE : ∀ i, Function.Bijective (relativeHomologyMap R i (j5cE_exMap V A')) :=
    fun i => b6m_closed_support_excision_bijective R hV hA'c.isClosed hA'V i
  have hinj : ∀ i, Function.Injective (fun β => relativeHomologyMap R i (j5cE_exMap V A')
      (relativeHomologyMap R i (j5cE_pairIso h A A' hAA').hom β)) :=
    fun i => (hexE i).1.comp (b6m_relativeHomologyMap_iso_injective R (j5cE_pairIso h A A' hAA') i)
  refine ⟨?_, ?_⟩
  · intro i hi
    have := ModuleCat.subsingleton_of_isZero (hEuc.1 i hi)
    have : Subsingleton (RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) i) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a', rfl⟩ := (hexM i).2 a
      obtain ⟨b', rfl⟩ := (hexM i).2 b
      have hab : a' = b' := hinj i (Subsingleton.elim _ _)
      rw [hab]
    exact ModuleCat.isZero_of_subsingleton _
  · intro α hα
    obtain ⟨β, rfl⟩ := (hexM n).2 α
    have hres : ∀ (u : U) (hu : (u : M) ∈ A),
        relativeHomologyMap R n (j5cE_resMap U (Set.singleton_subset_iff.mpr hu)) β = 0 := by
      intro u hu
      have hpt : Function.Injective (relativeHomologyMap R n (j5cE_exMap U {(u : M)})) :=
        (b6m_closed_support_excision_bijective R hU isClosed_singleton (Set.singleton_subset_iff.mpr u.2) n).1
      apply hpt
      have hsq := congrArg (fun f => relativeHomologyMap R n f β)
        (j5cE_exMap_comp_supportInclusion U (Set.singleton_subset_iff.mpr hu))
      simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hsq
      rw [← hsq, map_zero]
      exact hα u hu
    have hγ : relativeHomologyMap R n (j5cE_exMap V A')
        (relativeHomologyMap R n (j5cE_pairIso h A A' hAA').hom β) = 0 := by
      apply hEuc.2
      intro y hy
      obtain ⟨u, rfl⟩ : ∃ u : U, (h u : E) = y :=
        ⟨h.symm ⟨y, hA'V hy⟩, congrArg Subtype.val (h.apply_symm_apply _)⟩
      have hu : (u : M) ∈ A := (hAA' u).1 hy
      have hsq := congrArg (fun f => relativeHomologyMap R n f β)
        (j5cE_pairIso_chain h hAA' (j5cE_point_iff h u) (Set.singleton_subset_iff.mpr hu)
          (Set.singleton_subset_iff.mpr hy))
      simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hsq
      rw [hsq, hres u hu, map_zero, map_zero]
    have hIβ : relativeHomologyMap R n (j5cE_pairIso h A A' hAA').hom β = 0 :=
      (hexE n).1 (by rw [hγ, map_zero])
    have hβ0 : β = 0 :=
      b6m_relativeHomologyMap_iso_injective R (j5cE_pairIso h A A' hAA') n (by rw [hIβ, map_zero])
    rw [hβ0, map_zero]

theorem b6m_empty_local_homology {M E : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n) :
    (∀ k, n < k → IsZero (RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (∅ : Set M)ᶜ) k)) ∧
      (∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (∅ : Set M)ᶜ) n,
      (∀ (x : M) (hx : x ∈ (∅ : Set M)), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0) :=
  b6m_local_homology_of_homeomorph R hn isOpen_empty isOpen_empty (j5cE_emptyHomeomorph M E) isClosed_empty
    Set.Subset.rfl isCompact_empty Set.Subset.rfl fun u => absurd u.2 (Set.notMem_empty _)

theorem b6m_chart_local_homology {M E : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n)
    (e : OpenPartialHomeomorph M E) {A : Set M} (hA : IsCompact A) (hAe : A ⊆ e.source) :
    (∀ k, n < k → IsZero (RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) k)) ∧ (∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) n,
      (∀ (x : M) (hx : x ∈ A), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0) := by
  refine b6m_local_homology_of_homeomorph R hn e.open_source e.open_target (j5cE_sourceTargetHomeomorph e)
    hA.isClosed hAe (hA.image_of_continuousOn (e.continuousOn.mono hAe)) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hAe hx)
  · intro u
    rw [j5cE_sourceTargetHomeomorph_apply]
    constructor
    · rintro ⟨a, ha, hau⟩
      rw [← e.injOn (hAe ha) u.2 hau]
      exact ha
    · intro hu
      exact Set.mem_image_of_mem e hu

theorem b6m_iUnion_chart_local_homology {M E : Type} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {n : ℕ} (hn : Module.finrank ℝ E = n) {m : ℕ} (A : Fin m → Set M)
    (hA : ∀ j, IsCompact (A j)) (hchart : ∀ j, ∃ x : M, A j ⊆ (chartAt E x).source) :
    (∀ k, n < k → IsZero (RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (⋃ j, A j)ᶜ) k)) ∧
      (∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (⋃ j, A j)ᶜ) n,
      (∀ (x : M) (hx : x ∈ (⋃ j, A j)), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0) := by
  have key : ∀ (m : ℕ) (A : Fin m → Set M), (∀ j, IsCompact (A j)) →
      (∀ j, ∃ x : M, A j ⊆ (chartAt E x).source) →
      (∀ k, n < k → IsZero (RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (⋃ j, A j)ᶜ) k)) ∧
        (∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (⋃ j, A j)ᶜ) n,
      (∀ (x : M) (hx : x ∈ (⋃ j, A j)), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0) := by
    intro m
    induction m with
    | zero =>
      intro A _ _
      rw [Set.iUnion_eq_empty.2 fun j => Fin.elim0 j]
      exact b6m_empty_local_homology R hn
    | succ m ih =>
      intro A hA hchart
      have hU : (⋃ j : Fin (m + 1), A j) = A 0 ∪ ⋃ j : Fin m, A j.succ := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_union, Fin.exists_fin_succ]
      obtain ⟨x0, hx0⟩ := hchart 0
      have h0 := b6m_chart_local_homology R hn (chartAt E x0) (hA 0) hx0
      have h1 := ih (fun j => A j.succ) (fun j => hA _) (fun j => hchart _)
      have h01 := ih (fun j => A 0 ∩ A j.succ) (fun j => (hA 0).inter_right (hA _).isClosed)
        (fun j => ⟨x0, Set.inter_subset_left.trans hx0⟩)
      rw [← Set.inter_iUnion] at h01
      rw [hU]
      exact b6m_union_local_homology R n (hA 0).isClosed
        (isCompact_iUnion fun (j : Fin m) => hA j.succ).isClosed
        h0.1 h1.1 h01.1 h0.2 h1.2
  exact key m A hA hchart

theorem b6m_compact_manifold_local_homology {M E : Type} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {n : ℕ} (hn : Module.finrank ℝ E = n) {A : Set M} (hA : IsCompact A) :
    (∀ k, n < k → IsZero (RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) k)) ∧ (∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) Aᶜ) n,
      (∀ (x : M) (hx : x ∈ A), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0) := by
  classical
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun x : M => (chartAt E x).source)
    (fun x => (chartAt E x).open_source) (fun x _ => Set.mem_iUnion.2 ⟨x, mem_chart_source E x⟩)
  obtain ⟨K, hKc, hKU, hAK⟩ := hA.finite_compact_cover t (fun x : M => (chartAt E x).source)
    (fun x _ => (chartAt E x).open_source) ht
  have hEq : A = ⋃ j : Fin t.card, K (t.equivFin.symm j : M) := by
    rw [hAK]
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hy⟩
      exact ⟨t.equivFin ⟨i, hi⟩, by simpa using hy⟩
    · rintro ⟨j, hy⟩
      exact ⟨_, (t.equivFin.symm j).2, hy⟩
  rw [hEq]
  exact b6m_iUnion_chart_local_homology R hn _ (fun j => hKc _) (fun j => ⟨_, hKU _⟩)

end HodgeLean.Foundations.Program

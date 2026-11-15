import HodgeLean.Adapters.SupportedCycleClassesHelpers

/-!
Local restriction of finite weighted supported classes.
Source: Hatcher, Algebraic Topology, §3.1; Fulton, Intersection Theory, §19.1.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
open scoped BigOperators
namespace HodgeLean.Adapters.SupportedCycleClasses
/-- The identity on a neighbourhood as a map from larger to smaller allowed support. -/
def localSupportMap {M : Type} [TopologicalSpace M] (V S T : Set M)
    (h : ∀ x ∈ V, x ∈ S → x ∈ T) :
    neighborhoodSupportComplementPair V T ⟶ neighborhoodSupportComplementPair V S :=
  TopPair.ofHom (𝟙 (TopCat.of V))
    (TopCat.ofHom ⟨fun x => ⟨x.1, fun hx => x.2 (h x.1.1 x.1.2 hx)⟩, by fun_prop⟩)
    (by ext x; rfl)

/-- Restriction of an enlarged class is the enlargement of its neighbourhood restriction. -/
theorem enlargeSupport_restrict {M : Type} [TopologicalSpace M]
    (V S T : Set M) (hST : S ⊆ T) (n : ℕ)
    (c : CohomologyWithSupport ℚ (TopCat.of M) S n) :
    relativeCohomologyMap ℚ n (HodgeLean.Adapters.a3b4_neighborhoodPairMap V T)
      (enlargeSupport ℚ (TopCat.of M) hST n c) =
    relativeCohomologyMap ℚ n (localSupportMap V S T (fun x _ hx => hST hx))
      (relativeCohomologyMap ℚ n (HodgeLean.Adapters.a3b4_neighborhoodPairMap V S) c) := by
  unfold enlargeSupport
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  rfl

/-- Normal projection coclasses respect a change of allowed support and charts
that have equal coordinate values on the neighbourhood. -/
theorem localSupportMap_normalCoclass
    {M : Type} [TopologicalSpace M] (r k : ℕ) (V S T : Set M)
    (h : ∀ x ∈ V, x ∈ S → x ∈ T)
    (e f : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin k → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hT : ∀ y ∈ f.source, y ∈ T ↔ (f y).2 = 0)
    (hVe : V ⊆ e.source) (hVf : V ⊆ f.source)
    (hef : ∀ x ∈ V, e x = f x) :
    relativeCohomologyMap ℚ (2 * k) (localSupportMap V S T h)
      (chartNormalProjectionCoclass (Fin r → ℂ) k e S hS V hVe) =
      chartNormalProjectionCoclass (Fin r → ℂ) k f T hT V hVf := by
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  congr 1
  congr 1
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    apply Subtype.ext
    exact congrArg Prod.snd (hef x.1.1 x.1.2)
  · ext x
    exact congrArg Prod.snd (hef x.1 x.2)

/-- An enlarged class restricts to zero on any neighbourhood missing its original support. -/
theorem enlargeSupport_restrict_zero {M : Type} [TopologicalSpace M]
    (V S T : Set M) (hST : S ⊆ T) (n : ℕ)
    (hV : ∀ x ∈ V, x ∉ S) (c : CohomologyWithSupport ℚ (TopCat.of M) S n) :
    relativeCohomologyMap ℚ n (HodgeLean.Adapters.a3b4_neighborhoodPairMap V T)
      (enlargeSupport ℚ (TopCat.of M) hST n c) = 0 := by
  rw [enlargeSupport_restrict]
  letI := neighborhoodSupportRelativeCohomology_subsingleton (TopCat.of M) S n V hV
  have hz : relativeCohomologyMap ℚ n
      (HodgeLean.Adapters.a3b4_neighborhoodPairMap V S) c = 0 := Subsingleton.elim _ _
  rw [hz, map_zero]

/-- Near a single component the weighted supported representative restricts to
that component representative multiplied by its coefficient. -/
theorem weightedSum_restrict_single
    {ι : Type*} [Fintype ι] (X : TopCat.{0}) (n : ℕ) (S : ι → Set X) (T : Set X)
    (a : ι → ℚ) (hST : ∀ t, a t ≠ 0 → S t ⊆ T)
    (c : ∀ t, CohomologyWithSupport ℚ X (S t) n)
    (t : ι) (ha : a t ≠ 0) (V : Set X)
    (hV : ∀ s, s ≠ t → ∀ x ∈ V, x ∉ S s) :
    relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap V T)
      (SupportedClasses.weightedSum X n S T a hST c) =
    a t • relativeCohomologyMap ℚ n
      (localSupportMap V (S t) T (fun x _ hx => hST t ha hx))
      (relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap V (S t)) (c t)) := by
  classical
  unfold SupportedClasses.weightedSum
  rw [map_sum, Finset.sum_eq_single t]
  · simp only [dite_eq_left ha, map_smul]
    exact congrArg (fun z => a t • z)
      (enlargeSupport_restrict V (S t) T (hST t ha) n (c t))
  · intro s _ hst
    by_cases hs : a s ≠ 0
    · simp only [dite_eq_left hs, map_smul,
        enlargeSupport_restrict_zero V (S s) T (hST s hs) n (hV s hst), smul_zero]
    · simp only [dite_eq_right hs, map_zero]
  · intro h
    exact (h (Finset.mem_univ t)).elim

/-- A point in one of finitely many disjoint closed sets has an open neighbourhood
missing every other member of the family. -/
theorem disjoint_family_neighbourhood
    {M : Type} [TopologicalSpace M] {ι : Type*} [Fintype ι] (S : ι → Set M)
    (hclosed : ∀ t, IsClosed (S t))
    (hdisj : ∀ s t, s ≠ t → Disjoint (S s) (S t))
    (t : ι) (x : M) (hx : x ∈ S t) :
    ∃ V : Opens M, x ∈ V ∧ ∀ s, s ≠ t → ∀ y ∈ V, y ∉ S s := by
  let A : Set M := ⋃ s : ι, ⋃ (_ : s ≠ t), S s
  have hc : IsClosed A := isClosed_iUnion_of_finite fun s =>
    isClosed_iUnion_of_finite fun _ => hclosed s
  refine ⟨⟨Aᶜ, hc.isOpen_compl⟩, ?_, ?_⟩
  · intro h
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
    obtain ⟨hne, hxs⟩ := Set.mem_iUnion.mp hs
    exact Set.disjoint_left.mp (hdisj s t hne) hxs hx
  · intro s hne y hy hys
    exact hy (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hne, hys⟩⟩)

end HodgeLean.Adapters.SupportedCycleClasses

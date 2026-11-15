import HodgeLean.RealDefs.ComplexFundamentalClassProofs
import HodgeLean.RealDefs.FundamentalClass.Point
import HodgeLean.Foundations.QuotientDuality.LocalOrientationNaturality

/-! Gluing locally represented singular classes using detection on compact supports. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

/-- Compact-support detection suffices to glue any locally represented family.
Source: Hatcher, Algebraic Topology, proof of Theorem 3.26. -/
theorem hasClassAlong_compact_of_detection {M : Type} [TopologicalSpace M] [T2Space M]
    (n : ℕ)
    (hd : ∀ A : Set M, IsCompact A → LocalHomologyDetectedByPoints M n A)
    (μ : ∀ x : M, RelativeHomology ℚ (pointComplementPair x) n)
    (hμ : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (U : Set M)ᶜ) n,
        ∀ (y : M) (hy : y ∈ U), relativeHomologyMap ℚ n
          (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy)) c = μ y)
    {A : Set M} (hA : IsCompact A) : HasClassAlong M n μ A := by
  classical
  choose U hxU c hc using hμ
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun x : M => (U x : Set M))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  obtain ⟨K, hKc, hKU, hAK⟩ := hA.finite_compact_cover t (fun x : M => (U x : Set M))
    (fun x _ => (U x).isOpen) ht
  have key : ∀ s : Finset M, HasClassAlong M n μ (⋃ i ∈ s, K i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact ⟨0, fun x hx => by simp at hx⟩
    · intro a s _ ih
      rw [Finset.set_biUnion_insert]
      have hB := s.isCompact_biUnion (fun i _ => hKc i)
      exact j5c_union_hasClassAlong_aux n (hKc a).isClosed hB.isClosed μ
        (j5cE_hasClassAlong_mono (hKU a) ⟨c a, fun y hy => hc a y hy⟩) ih
        (hd _ ((hKc a).inter_right hB.isClosed))
  rw [hAK]
  exact key t

/-- Detection on compact supports turns a coherent orientation into a unique absolute class.
Source: Hatcher, Algebraic Topology, proof of Theorem 3.26. -/
theorem fundamental_class_of_compact_detection (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (n : ℕ) (o : LocalRationalOrientation X n)
    (hd : ∀ A : Set X, IsCompact A → LocalHomologyDetectedByPoints X n A) :
    ∃! c : Homology ℚ X n, ∀ x, localOrientation X n c x = o.generator x := by
  let A := TopPair.ofSubset (X := X) ((((⊤ : Opens X) : Set X)ᶜ) : Set X)
  letI : IsIso (relativeChainProjection ℚ A) :=
    isIso_relativeChainProjection _ ⟨fun y => y.2 trivial⟩
  letI : IsIso (relativeHomologyProjection ℚ A n) := by
    unfold relativeHomologyProjection
    infer_instance
  have hp : Function.Bijective (relativeHomologyProjection ℚ A n).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hn (v : Homology ℚ X n) (y : X) :
      relativeHomologyMap ℚ n
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr (Opens.mem_top y)))
        ((relativeHomologyProjection ℚ A n).hom v) = localOrientation X n v y := by
    have h := relativeHomologyProjection_map n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr (Opens.mem_top y))) v
    have hi : (supportInclusionPairMap X
        (Set.singleton_subset_iff.mpr (Opens.mem_top y))).hom.right = 𝟙 X := rfl
    rw [hi] at h
    erw [homologyMap_id] at h
    exact h
  obtain ⟨w, hw⟩ := hasClassAlong_compact_of_detection n hd o.generator o.coherent
    (A := ((⊤ : Opens X) : Set X)) isCompact_univ
  obtain ⟨c, hc⟩ := hp.2 w
  have hlocal : ∀ x, localOrientation X n c x = o.generator x := by
    intro x
    rw [← hn c x, hc]
    exact hw x (Opens.mem_top x)
  refine ⟨c, hlocal, fun c' hc' => hp.1 ?_⟩
  apply sub_eq_zero.mp
  apply hd _ isCompact_univ
  intro x hx
  rw [map_sub]
  apply sub_eq_zero.mpr
  exact (hn c' x).trans ((hc' x).trans ((hlocal x).symm.trans (hn c x).symm))

#print axioms hasClassAlong_compact_of_detection
#print axioms fundamental_class_of_compact_detection

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseNeighbourhoodSquares
import HodgeLean.Foundations.QuotientDuality.PersistenceSimultaneousShrink

/-! Actual locus-collapse comparison from ambient deformation and controlled exact sequences. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_ambient_collapse_relative_homology_bijective
    (K : Type) [CommRing K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    (A P : Set X) (hA : IsClosed A) (hP : IsOpen P) (hAP : A ⊆ P) (r : C(X, X))
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hfixed : ∀ (t : unitInterval) a, a ∈ A → H (t, a) = a)
    (hret : ∀ x ∈ P, r x ∈ A) (a : X) (ha : a ∈ A) (n : ℕ) :
    Function.Bijective (relativeHomologyMap K n (persistenceCollapseLocusPairMap A a ha)) := by
  let q := Quotient.mk (persistenceCollapseSetoid A)
  let B : Set (Quotient (persistenceCollapseSetoid A)) := {q a}
  obtain ⟨N, hN, hAN, hqN, hNU, hNzero⟩ :=
    persistence_simultaneous_relative_homology_shrink K A P hP hAP r H hfixed hret
      Set.univ isOpen_univ (Set.subset_univ A) a ha
  obtain ⟨M, hM, hAM, hqM, hMN, hMzero⟩ :=
    persistence_simultaneous_relative_homology_shrink K A P hP hAP r H hfixed hret
      N hN hAN a ha
  have hBM : B ⊆ q '' M := by
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact ⟨a, hAM ha, rfl⟩
  have hBN : B ⊆ q '' N := by
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact ⟨a, hAN ha, rfl⟩
  let c := relativeHomologyMap K n (persistenceCollapseLocusPairMap A a ha)
  let cM := relativeHomologyMap K n (persistenceCollapseNeighbourhoodPairMap A M)
  let cN := relativeHomologyMap K n (persistenceCollapseNeighbourhoodPairMap A N)
  let pM := relativeHomologyMap K n (persistenceSubsetEnlargementMap A M hAM)
  let pN := relativeHomologyMap K n (persistenceSubsetEnlargementMap A N hAN)
  let pQM := relativeHomologyMap K n (persistenceSubsetEnlargementMap B (q '' M) hBM)
  let pQN := relativeHomologyMap K n (persistenceSubsetEnlargementMap B (q '' N) hBN)
  let jMN := relativeHomologyMap K n (persistenceSubsetEnlargementMap M N hMN)
  let jQMN := relativeHomologyMap K n
    (persistenceSubsetEnlargementMap (q '' M) (q '' N) (Set.image_mono hMN))
  have hpM : Function.Injective pM :=
    persistence_subset_enlargement_relative_homology_injective_of_shrink K A M N hAM hMN n
      (hMzero n).1
  have hcM : Function.Bijective cM :=
    persistence_collapse_neighbourhood_relative_homology_bijective K A M hA hM hAM n
  have hpQN : Function.Injective pQN :=
    persistence_subset_enlargement_relative_homology_injective_of_shrink K B (q '' N)
      (q '' Set.univ) hBN (Set.image_mono hNU) n (hNzero n).2
  have hdM := congrArg (relativeHomologyMap K n)
    (persistence_collapse_enlargement_square A M hAM a ha)
  have hdN := congrArg (relativeHomologyMap K n)
    (persistence_collapse_enlargement_square A N hAN a ha)
  have hdMN := congrArg (relativeHomologyMap K n)
    (persistence_collapse_neighbourhood_enlargement_square A M N hMN)
  have hdQ := congrArg (relativeHomologyMap K n)
    (persistence_subset_enlargement_comp B (q '' M) (q '' N) hBM (Set.image_mono hMN))
  rw [relativeHomologyMap_comp, relativeHomologyMap_comp] at hdM hdN hdMN
  rw [relativeHomologyMap_comp] at hdQ
  have hcommM : cM ∘ₗ pM = pQM ∘ₗ c := hdM
  have hcommN : cN ∘ₗ pN = pQN ∘ₗ c := hdN
  have hcommMN : cN ∘ₗ jMN = jQMN ∘ₗ cM := hdMN
  have hcompQ : jQMN ∘ₗ pQM = pQN := hdQ
  change Function.Bijective c
  refine ⟨?_, ?_⟩
  · intro u v huv
    apply hpM
    apply hcM.injective
    have hu : cM (pM u) = pQM (c u) := LinearMap.congr_fun hcommM u
    have hv : cM (pM v) = pQM (c v) := LinearMap.congr_fun hcommM v
    change cM (pM u) = cM (pM v)
    rw [hu, hv]
    exact congrArg pQM huv
  · intro w
    obtain ⟨uM, huM⟩ := hcM.surjective (pQM w)
    obtain ⟨v, hv⟩ := persistence_nested_triple_relative_homology_lift K A M N hAM hMN n
      (fun k => (hMzero k).1) uM
    change pN v = jMN uM at hv
    refine ⟨v, ?_⟩
    apply hpQN
    calc
      pQN (c v) = cN (pN v) := (LinearMap.congr_fun hcommN v).symm
      _ = cN (jMN uM) := congrArg cN hv
      _ = jQMN (cM uM) := LinearMap.congr_fun hcommMN uM
      _ = jQMN (pQM w) := congrArg jQMN huM
      _ = pQN w := LinearMap.congr_fun hcompQ w

end HodgeLean.Foundations.QuotientDuality

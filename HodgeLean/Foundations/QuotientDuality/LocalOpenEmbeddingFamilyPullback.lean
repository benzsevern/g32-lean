import HodgeLean.Foundations.QuotientDuality.LocalPointClassLift
import HodgeLean.Foundations.QuotientDuality.LocalClassAgreementNeighborhood
import HodgeLean.Foundations.QuotientDuality.LocalOpenEmbeddingOrientationFamily
import HodgeLean.Foundations.QuotientDuality.LocalOpenEmbeddingPointHomology

/-! Pulling locally represented families back through open embeddings. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

theorem openEmbedding_family_locally_represented_pullback
    {X Y : TopCat.{0}} [T2Space X] [T2Space Y]
    (f : X ⟶ Y) (hf : IsOpenEmbedding f) (n : ℕ)
    (S : Type) (j : S → X)
    (μ : ∀ s, orientationGroup X n (j s))
    (ν : ∀ s, orientationGroup Y n (f (j s)))
    (hcompat : ∀ s, relativeHomologyMap ℚ n
      (imagePointPairMap f hf.injective (j s)) (μ s) = ν s)
    (hν : ∀ s, ∃ (V : Opens Y), f (j s) ∈ V ∧
      ∃ w : RelativeHomology ℚ (TopPair.ofSubset (X := Y) (V : Set Y)ᶜ) n,
        ∀ (t : S) (ht : f (j t) ∈ V), relativeHomologyMap ℚ n
          (supportInclusionPairMap Y (Set.singleton_subset_iff.mpr ht)) w = ν t) :
    ∀ s, ∃ (U : Opens X), j s ∈ U ∧
      ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ) n,
        ∀ (t : S) (ht : j t ∈ U), relativeHomologyMap ℚ n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr ht)) c = μ t := by
  intro s
  obtain ⟨U, hsU, c, hc⟩ := point_class_open_lift X n (j s) (μ s)
  obtain ⟨V, hsV, w, hw⟩ := hν s
  let F : Opens Y := ⟨f '' (U : Set X), hf.isOpenMap _ U.isOpen⟩
  let cF := relativeHomologyMap ℚ n (imageSupportPairMap f hf.injective (U : Set X)) c
  have hsF : f (j s) ∈ F := ⟨j s, hsU, rfl⟩
  have hpoint (t : S) (ht : j t ∈ U) : relativeHomologyMap ℚ n
      (supportInclusionPairMap Y (Set.singleton_subset_iff.mpr (show f (j t) ∈ F from ⟨j t, ht, rfl⟩))) cF =
      relativeHomologyMap ℚ n (imagePointPairMap f hf.injective (j t))
        (relativeHomologyMap ℚ n (supportInclusionPairMap X (Set.singleton_subset_iff.mpr ht)) c) := by
    have H := congrArg (fun g => relativeHomologyMap ℚ n g c)
      (imageSupportPairMap_restrict f hf.injective (U : Set X) (j t) ht)
    rw [relativeHomologyMap_comp, relativeHomologyMap_comp,
      LinearMap.comp_apply, LinearMap.comp_apply] at H
    exact H
  obtain ⟨W, hsW, hWF, hWV, heq⟩ := supported_classes_agree_near_point Y n F V
    (f (j s)) hsF hsV cF w (by
      exact (hpoint s hsU).trans ((congrArg
        (relativeHomologyMap ℚ n (imagePointPairMap f hf.injective (j s))) hc).trans
          ((hcompat s).trans (hw s hsV).symm)))
  let U' : Opens X := U ⊓ ⟨f ⁻¹' (W : Set Y), W.isOpen.preimage hf.continuous⟩
  refine ⟨U', ⟨hsU, hsW⟩,
    relativeHomologyMap ℚ n (supportInclusionPairMap X (inf_le_left : U' ≤ U)) c, ?_⟩
  intro t ht
  apply (openEmbedding_point_homology_bijective f hf (j t) n).injective
  have H := congrArg (relativeHomologyMap ℚ n
    (supportInclusionPairMap Y (Set.singleton_subset_iff.mpr ht.2))) heq
  have H' := (support_restriction_trans Y (Set.singleton_subset_iff.mpr ht.2) hWF n cF).symm.trans
    (H.trans (support_restriction_trans Y (Set.singleton_subset_iff.mpr ht.2) hWV n w))
  exact (congrArg (relativeHomologyMap ℚ n (imagePointPairMap f hf.injective (j t)))
    (support_restriction_trans X (Set.singleton_subset_iff.mpr ht)
      (inf_le_left : U' ≤ U) n c)).trans
        ((hpoint t ht.1).symm.trans (H'.trans ((hw t (hWV ht.2)).trans (hcompat t).symm)))

#print axioms openEmbedding_family_locally_represented_pullback
end HodgeLean.Foundations.QuotientDuality

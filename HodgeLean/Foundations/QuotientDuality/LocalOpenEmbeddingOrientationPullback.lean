import HodgeLean.Foundations.QuotientDuality.LocalOpenEmbeddingFamilyPullback

/-! Coherent orientations restrict along arbitrary open embeddings. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

def openEmbeddingPointHomologyEquiv {X Y : TopCat.{0}} [T1Space Y]
    (f : X ⟶ Y) (hf : IsOpenEmbedding f) (x : X) (n : ℕ) :
    orientationGroup X n x ≃ₗ[ℚ] orientationGroup Y n (f x) :=
  LinearEquiv.ofBijective _ (openEmbedding_point_homology_bijective f hf x n)

def openEmbeddingOrientationPullback {X Y : TopCat.{0}} [T2Space X] [T2Space Y]
    (f : X ⟶ Y) (hf : IsOpenEmbedding f) (n : ℕ)
    (o : LocalRationalOrientation Y n) : LocalRationalOrientation X n where
  generator x := (openEmbeddingPointHomologyEquiv f hf x n).symm (o.generator (f x))
  generates x := by
    let E := openEmbeddingPointHomologyEquiv f hf x n
    have H : (fun q : ℚ => E.symm (q • o.generator (f x))) =
        (fun q : ℚ => q • E.symm (o.generator (f x))) := by
      funext q
      exact map_smul _ _ _
    change Function.Bijective (fun q : ℚ => q • E.symm (o.generator (f x)))
    rw [← H]
    exact E.symm.bijective.comp (o.generates (f x))
  vanishes x i hi := by
    letI := o.vanishes (f x) i hi
    exact (openEmbeddingPointHomologyEquiv f hf x i).injective.subsingleton
  coherent := by
    apply openEmbedding_family_locally_represented_pullback f hf n X id
      (fun x => (openEmbeddingPointHomologyEquiv f hf x n).symm (o.generator (f x)))
      (fun x => o.generator (f x))
    · intro x
      exact (openEmbeddingPointHomologyEquiv f hf x n).apply_symm_apply _
    · intro x
      obtain ⟨V, hxV, w, hw⟩ := o.coherent (f x)
      exact ⟨V, hxV, w, fun t ht => hw (f t) ht⟩

theorem openEmbeddingOrientationPullback_generator {X Y : TopCat.{0}}
    [T2Space X] [T2Space Y] (f : X ⟶ Y) (hf : IsOpenEmbedding f) (n : ℕ)
    (o : LocalRationalOrientation Y n) (x : X) :
    relativeHomologyMap ℚ n (imagePointPairMap f hf.injective x)
      ((openEmbeddingOrientationPullback f hf n o).generator x) = o.generator (f x) :=
  (openEmbeddingPointHomologyEquiv f hf x n).apply_symm_apply _

#print axioms openEmbeddingOrientationPullback
#print axioms openEmbeddingOrientationPullback_generator
end HodgeLean.Foundations.QuotientDuality

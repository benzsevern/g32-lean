import HodgeLean.Foundations.QuotientDuality.LocalChartEmbedding

/-! Locally represented orientation families transported by an open embedding. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsOpenEmbedding f)
    (n : ℕ) (o : LocalRationalOrientation X n)

def openEmbeddingOrientationFamily (x : X) : orientationGroup Y n (f x) :=
  relativeHomologyMap ℚ n (imagePointPairMap f hf.injective x) (o.generator x)

theorem openEmbeddingOrientationFamily_locally_represented (x : X) :
    ∃ (V : Opens Y), f x ∈ V ∧
      ∃ w : RelativeHomology ℚ (TopPair.ofSubset (X := Y) (V : Set Y)ᶜ) n,
        ∀ (t : X) (ht : f t ∈ V), relativeHomologyMap ℚ n
          (supportInclusionPairMap Y (Set.singleton_subset_iff.mpr ht)) w =
            openEmbeddingOrientationFamily f hf n o t := by
  obtain ⟨U, hxU, c, hc⟩ := o.coherent x
  let V : Opens Y := ⟨f '' (U : Set X), hf.isOpenMap _ U.isOpen⟩
  let w := relativeHomologyMap ℚ n (imageSupportPairMap f hf.injective (U : Set X)) c
  refine ⟨V, ⟨x, hxU, rfl⟩, w, ?_⟩
  intro t ht
  have htU : t ∈ U := by
    obtain ⟨a, ha, he⟩ := ht
    exact (hf.injective he) ▸ ha
  have H := congrArg (fun g => relativeHomologyMap ℚ n g c)
    (imageSupportPairMap_restrict f hf.injective (U : Set X) t htU)
  rw [relativeHomologyMap_comp, relativeHomologyMap_comp,
    LinearMap.comp_apply, LinearMap.comp_apply] at H
  exact H.trans (congrArg (relativeHomologyMap ℚ n (imagePointPairMap f hf.injective t)) (hc t htU))

#print axioms openEmbeddingOrientationFamily
#print axioms openEmbeddingOrientationFamily_locally_represented
end HodgeLean.Foundations.QuotientDuality

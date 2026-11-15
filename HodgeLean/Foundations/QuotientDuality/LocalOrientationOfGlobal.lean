import HodgeLean.Foundations.QuotientDuality.LocalOrientationNaturality

/-! Global classes with generating local restrictions supply coherent orientation data. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

def localOrientationOfGlobal (X : TopCat.{0}) (n : ℕ) (c : Homology ℚ X n)
    (hgen : ∀ x, Function.Bijective (orientationLine X n c x))
    (hvanish : ∀ x i, i ≠ n → Subsingleton (orientationGroup X i x)) :
    LocalRationalOrientation X n where
  generator := localOrientation X n c
  generates := hgen
  vanishes := hvanish
  coherent := by
    intro x
    let A := TopPair.ofSubset ((((⊤ : Opens X) : Set X)ᶜ) : Set X)
    refine ⟨⊤, Opens.mem_top x, (relativeHomologyProjection ℚ A n).hom c, ?_⟩
    intro y hy
    have hn := relativeHomologyProjection_map n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hy)) c
    have hi : (supportInclusionPairMap X
        (Set.singleton_subset_iff.mpr hy)).hom.right = 𝟙 X := rfl
    rw [hi] at hn
    erw [homologyMap_id] at hn
    exact hn

#print axioms localOrientationOfGlobal
end HodgeLean.Foundations.QuotientDuality

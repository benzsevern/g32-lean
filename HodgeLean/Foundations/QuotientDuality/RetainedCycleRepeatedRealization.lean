import HodgeLean.Foundations.QuotientDuality.RetainedCycleFullNormalization
import HodgeLean.Foundations.QuotientDuality.RetainedCycleSupportedFibres
import HodgeLean.Foundations.QuotientDuality.RetainedCycleCollectedClassAlgebra
import HodgeLean.Foundations.QuotientDuality.RetainedCycleSupportReflection

/-! Weighted prime realization from equality of repeated supported occurrences. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Classical
namespace HodgeLean.Foundations.QuotientDuality

/-- Compatible repeated prime classes realize their collected cycle with its original chart normalization. -/
lemma retained_weighted_realization_of_supported_repeats
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*k+2*k) c x))
    (hv : ∀ j : ℕ, j ≠ 2*(2*k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    {I : Type} [Fintype I] (ξ : I → X.left) (hc : ∀ i, Order.coheight (ξ i) = k)
    (a : ∀ i, s2e_supportedClass X (properPrime (ξ i)) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (properPrime (ξ i)) k (a i))
    (hrepeat : ∀ i j, ξ i = ξ j → HEq (a i) (a j)) (q : I → ℚ) :
    let Γ : AlgebraicCycle X.left ℚ := ∑ i, (properPrime (ξ i)).mapRange (q i * ·) (mul_zero _)
    let T : Set (ComplexPoint X) := ⋃ i, a3b4_cycleSupport X.hom (properPrime (ξ i))
    ∃ (hΓ : a3b4_cycleSupport X.hom Γ ⊆ T)
      (hi : ∀ i, a3b4_cycleSupport X.hom (properPrime (ξ i)) ⊆ T)
      (b : s2e_supportedClass X Γ k),
      a3b4_IsCycleClass X.hom Γ k b ∧
      enlargeSupport ℚ (a3b4_an X.hom) hΓ (2*k) b =
        ∑ i, q i • enlargeSupport ℚ (a3b4_an X.hom) (hi i) (2*k) (a i) := by
  let Γ : AlgebraicCycle X.left ℚ := ∑ i, (properPrime (ξ i)).mapRange (q i * ·) (mul_zero _)
  let T : Set (ComplexPoint X) := ⋃ i, a3b4_cycleSupport X.hom (properPrime (ξ i))
  let hΓ : a3b4_cycleSupport X.hom Γ ⊆ T := retained_prime_collection_support X ξ q
  let hi : ∀ i, a3b4_cycleSupport X.hom (properPrime (ξ i)) ⊆ T :=
    fun i => Set.subset_iUnion (fun i => a3b4_cycleSupport X.hom (properPrime (ξ i))) i
  have hSA : ∀ p ∈ Finset.univ.image ξ,
      (∑ i with ξ i = p, q i) ≠ 0 →
      a3b4_cycleSupport X.hom (properPrime p) ⊆ a3b4_cycleSupport X.hom Γ := by
    intro p _ hq z hz
    have hp : p ∈ Γ.support := by
      change Γ p ≠ 0
      rw [retained_prime_collection_coefficient]
      exact hq
    exact Set.mem_iUnion₂.mpr ⟨p, hp, (retained_prime_support_iff X p z).mp hz⟩
  obtain ⟨b, hb⟩ := retained_supported_descent_of_repeats (a3b4_an X.hom) (2*k)
    ξ q (fun p => a3b4_cycleSupport X.hom (properPrime p)) a hrepeat
    (a3b4_cycleSupport X.hom Γ) T hΓ hi hSA
  refine ⟨hΓ, hi, b, ?_, hb⟩
  apply retained_full_carrier_lift_normalized X k hk hdim c ho hv
    (fun i => properPrime (ξ i)) q ?_ a ha b hΓ hi hb
  intro i η hη
  have he : η = ξ i := by
    by_contra hn
    exact hη (by simp [properPrime, hn])
  simpa only [he] using hc i

end HodgeLean.Foundations.QuotientDuality

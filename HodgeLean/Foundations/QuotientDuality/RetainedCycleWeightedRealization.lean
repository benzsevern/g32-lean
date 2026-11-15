import HodgeLean.Foundations.QuotientDuality.RetainedCycleWeightedSmooth

/-! Finite normalized collection on the full union carrier. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Classical
namespace HodgeLean.Foundations.QuotientDuality

/-- Smooth finite families retain their exact weighted class on the full union, in every middle degree. -/
lemma retained_smooth_weighted_full_carrier
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom] [Smooth X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2 * k)
    (hv : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ)
    (hc : ∀ i ξ, ξ ∈ (γ i).support → Order.coheight ξ = k)
    (a : ∀ i, s2e_supportedClass X (γ i) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) k (a i)) (q : I → ℚ) :
    let Γ : AlgebraicCycle X.left ℚ := ∑ i, (γ i).mapRange (q i * ·) (mul_zero _)
    let T : Set (ComplexPoint X) := ⋃ i, a3b4_cycleSupport X.hom (γ i)
    ∃ (hΓ : a3b4_cycleSupport X.hom Γ ⊆ T)
      (hi : ∀ i, a3b4_cycleSupport X.hom (γ i) ⊆ T)
      (b : s2e_supportedClass X Γ k),
      a3b4_IsCycleClass X.hom Γ k b ∧
      enlargeSupport ℚ (a3b4_an X.hom) hΓ (2 * k) b =
        ∑ i, q i • enlargeSupport ℚ (a3b4_an X.hom) (hi i) (2 * k) (a i) := by
  have hdescent :
      ∃ b : s2e_supportedClass X (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) k,
        a3b4_IsCycleClass X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) k b ∧
        enlargeSupport ℚ (a3b4_an X.hom) (properCycle_collected_support_subset X γ q) (2*k) b =
          SupportedClasses.weightedSum (a3b4_an X.hom) (2*k)
            (fun i => a3b4_cycleSupport X.hom (γ i))
            (⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)) q
            (fun i hi z hz => Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩) a := by
    by_cases hk : k = 0
    · subst k
      have hd : TopologicalSpace.dim X.left = 0 := by simpa only [mul_zero] using hdim
      exact properCycle_zero_dimension_collected_descent X hd γ
        (fun i ξ hξ => retained_zero_dimension_cycle_charts X hd (γ i) ξ hξ) a ha q
    · exact properCycle_smooth_normalized_collected_descent X k (Nat.pos_of_ne_zero hk)
        hdim hv γ q hc a ha
  obtain ⟨b, hb, he⟩ := hdescent
  have hΓ : a3b4_cycleSupport X.hom
      (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) ⊆
      ⋃ i, a3b4_cycleSupport X.hom (γ i) := by
    intro z hz
    obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp (properCycle_collected_support_subset X γ q hz)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  refine ⟨hΓ, fun i => Set.subset_iUnion (fun i => a3b4_cycleSupport X.hom (γ i)) i,
    b, hb, ?_⟩
  exact retained_weighted_active_to_full (a3b4_an X.hom) (2*k)
    (fun i => a3b4_cycleSupport X.hom (γ i)) q a _
    (properCycle_collected_support_subset X γ q) b he

end HodgeLean.Foundations.QuotientDuality

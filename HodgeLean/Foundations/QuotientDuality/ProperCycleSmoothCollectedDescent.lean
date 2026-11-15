import HodgeLean.Foundations.QuotientDuality.ProperCycleFamilyChartDescent
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothFamilyCharts
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothCollectedNormalization

/-! # Exact normalized collected descent in smooth ambient schemes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- Independent normalized rational cycle representatives in a smooth ambient scheme descend to the original normalized class on the collected support, with exact support enlargement.
Source: Fulton, Intersection Theory, sections 1.5 and 19.1; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_smooth_normalized_collected_descent
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom] [Smooth X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2 * k)
    (hvan : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (hcodim : ∀ i ξ, ξ ∈ (γ i).support → Order.coheight ξ = k)
    (a : ∀ i, s2e_supportedClass X (γ i) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) k (a i)) :
    let Γ : AlgebraicCycle X.left ℚ := ∑ i, (γ i).mapRange (q i * ·) (mul_zero _)
    let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
    let hT : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T :=
      fun i hi y hy => Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩
    ∃ s : s2e_supportedClass X Γ k, a3b4_IsCycleClass X.hom Γ k s ∧
      enlargeSupport ℚ (a3b4_an X.hom) (properCycle_collected_support_subset X γ q) (2 * k) s =
        SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
          (fun i => a3b4_cycleSupport X.hom (γ i)) T q hT a := by
  have hlow : ∀ i ξ, ξ ∈ (γ i).support → (k : ℕ∞) ≤ Order.coheight ξ :=
    fun i ξ hi => (hcodim i ξ hi).ge
  obtain ⟨s, hs⟩ := properCycle_collected_supported_lift_of_regular_chart_cover X k hk hdim hvan
    γ q hlow a ha (properCycle_smooth_family_regular_chart_cover X γ q k hlow)
  exact ⟨s, properCycle_smooth_collected_lift_normalized X k hk hdim hvan γ q hcodim a ha s hs, hs⟩

end HodgeLean.Foundations.QuotientDuality

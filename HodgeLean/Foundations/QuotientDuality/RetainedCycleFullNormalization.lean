import HodgeLean.Foundations.QuotientDuality.RetainedCycleActiveDetection
import HodgeLean.Foundations.QuotientDuality.RetainedCycleCollectedNormalization

/-! Normalization recovered from the full common-carrier equation. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Classical
namespace HodgeLean.Foundations.QuotientDuality

/-- An exact full-carrier lift retains the original normalization, including in a singular ambient scheme. -/
lemma retained_full_carrier_lift_normalized
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*k+2*k) c x))
    (hv : ∀ j : ℕ, j ≠ 2*(2*k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (hc : ∀ i ξ, ξ ∈ (γ i).support → Order.coheight ξ = k)
    (a : ∀ i, s2e_supportedClass X (γ i) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) k (a i))
    (b : s2e_supportedClass X (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) k)
    (hΓ : a3b4_cycleSupport X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) ⊆
      ⋃ i, a3b4_cycleSupport X.hom (γ i))
    (hi : ∀ i, a3b4_cycleSupport X.hom (γ i) ⊆ ⋃ i, a3b4_cycleSupport X.hom (γ i))
    (hs : enlargeSupport ℚ (a3b4_an X.hom) hΓ (2*k) b =
      ∑ i, q i • enlargeSupport ℚ (a3b4_an X.hom) (hi i) (2*k) (a i)) :
    a3b4_IsCycleClass X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) k b := by
  let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
  let U := ⋃ i, a3b4_cycleSupport X.hom (γ i)
  have hTU : T ⊆ U := by
    intro z hz
    obtain ⟨i, _, hzi⟩ := Set.mem_iUnion₂.mp hz
    exact Set.mem_iUnion.mpr ⟨i, hzi⟩
  let hST : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T :=
    fun i hqi z hz => Set.mem_iUnion₂.mpr ⟨i, hqi, hz⟩
  let w := SupportedClasses.weightedSum (a3b4_an X.hom) (2*k)
    (fun i => a3b4_cycleSupport X.hom (γ i)) T q hST a
  have hw : enlargeSupport ℚ (a3b4_an X.hom) hTU (2*k) w =
      ∑ i, q i • enlargeSupport ℚ (a3b4_an X.hom) (hi i) (2*k) (a i) := by
    dsimp only [w]
    rw [properCycle_enlarge_weightedSum]
    unfold SupportedClasses.weightedSum
    apply Finset.sum_congr rfl
    intro i _
    by_cases hqi : q i ≠ 0
    · rw [dite_eq_left hqi]
    · rw [dite_eq_right hqi, not_ne_iff.mp hqi, zero_smul]
  have hvan : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x) := by
    intro j hj
    exact hv j (by omega)
  have hinj := retained_active_to_full_injective X k hk hdim γ q hc c ho hvan hTU
  apply retained_collected_lift_normalized X k hk hdim hv γ q hc a ha b
  apply hinj
  have hcomp : enlargeSupport ℚ (a3b4_an X.hom) hTU (2*k)
      (enlargeSupport ℚ (a3b4_an X.hom) (properCycle_collected_support_subset X γ q) (2*k) b) =
      enlargeSupport ℚ (a3b4_an X.hom) hΓ (2*k) b := by
    unfold enlargeSupport
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
    rfl
  exact hcomp.trans (hs.trans hw.symm)

end HodgeLean.Foundations.QuotientDuality

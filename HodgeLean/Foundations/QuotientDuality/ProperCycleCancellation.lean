import HodgeLean.Foundations.QuotientDuality.ProperCycleCollection
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalization

/-! # Exact supported cancellation of repeated cycle representatives -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- Repeated copies of the same representative cancel on the union support at total weight zero.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1, rational linearity;
Hatcher, Algebraic Topology, section 3.1, linearity of relative cohomology.
HC no distance; AV milestone no distance. -/
lemma properCycle_same_class_zero_sum_descent
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (k : ℕ)
    {I : Type} [Fintype I] (δ : AlgebraicCycle X.left ℚ)
    (a : s2e_supportedClass X δ k) (q : I → ℚ) (hsum : ∑ i, q i = 0) :
    let γ : I → AlgebraicCycle X.left ℚ := fun _ => δ
    let Γ : AlgebraicCycle X.left ℚ := ∑ i, (γ i).mapRange (q i * ·) (mul_zero _)
    let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
    let hT : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T :=
      fun i hi z hz => Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩
    ∃ s : s2e_supportedClass X Γ k,
      a3b4_IsCycleClass X.hom Γ k s ∧
      enlargeSupport ℚ (a3b4_an X.hom)
        (properCycle_collected_support_subset X γ q) (2 * k) s =
      SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
        (fun i => a3b4_cycleSupport X.hom (γ i)) T q hT (fun _ => a) := by
  classical
  dsimp only
  have hΓ : (∑ i : I, δ.mapRange (q i * ·) (mul_zero _)) = 0 := by
    ext ξ
    simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Function.locallyFinsuppWithin.mapRange_apply]
    change (∑ i, q i * δ ξ) = 0
    rw [← Finset.sum_mul, hsum, zero_mul]
  let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom δ
  let hT : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom δ ⊆ T :=
    fun i hi z hz => Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩
  have hw : SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
      (fun _ : I => a3b4_cycleSupport X.hom δ) T q hT (fun _ => a) = 0 := by
    by_cases hactive : ∃ i, q i ≠ 0
    · obtain ⟨j, hj⟩ := hactive
      let hS := hT j hj
      have heq : SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
          (fun _ : I => a3b4_cycleSupport X.hom δ) T q hT (fun _ => a) =
          (∑ i, q i) • enlargeSupport ℚ (a3b4_an X.hom) hS (2 * k) a := by
        unfold SupportedClasses.weightedSum
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with hi
        · rfl
        · rw [not_ne_iff.mp hi, zero_smul]
      rw [heq, hsum, zero_smul]
    · have hq : ∀ i, q i = 0 := fun i => not_ne_iff.mp (fun hi => hactive ⟨i, hi⟩)
      simp [SupportedClasses.weightedSum, hq]
  have hn : a3b4_IsCycleClass X.hom
      (∑ i : I, δ.mapRange (q i * ·) (mul_zero _)) k 0 := by
    rw [hΓ]
    exact properCycle_zero_normalized X k
  refine ⟨0, hn, ?_⟩
  rw [map_zero, hw]

/-- A family with no nonzero weighted cycle has zero collected class on its literal union support.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1, rational linearity;
Hatcher, Algebraic Topology, section 3.1, empty-support relative cohomology.
HC no distance; AV milestone no distance. -/
lemma properCycle_inactive_terms_descent
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (k : ℕ)
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ)
    (a : ∀ i, s2e_supportedClass X (γ i) k) (q : I → ℚ)
    (hzero : ∀ i, q i = 0 ∨ γ i = 0) :
    let Γ : AlgebraicCycle X.left ℚ := ∑ i, (γ i).mapRange (q i * ·) (mul_zero _)
    let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
    let hT : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T :=
      fun i hi z hz => Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩
    ∃ s : s2e_supportedClass X Γ k,
      a3b4_IsCycleClass X.hom Γ k s ∧
      enlargeSupport ℚ (a3b4_an X.hom)
        (properCycle_collected_support_subset X γ q) (2 * k) s =
      SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
        (fun i => a3b4_cycleSupport X.hom (γ i)) T q hT a := by
  classical
  dsimp only
  have hΓ : (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rcases hzero i with hi | hi
    · ext x; simp [hi]
    · rw [hi]; ext x; simp
  have hn : a3b4_IsCycleClass X.hom
      (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) k 0 := by
    rw [hΓ]
    exact properCycle_zero_normalized X k
  refine ⟨0, hn, ?_⟩
  rw [map_zero]
  symm
  unfold SupportedClasses.weightedSum
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · have hγ : γ i = 0 := (hzero i).resolve_left hi
    have hai : ∀ d : s2e_supportedClass X (γ i) k, d = 0 := by
      rw [hγ]
      exact properCycle_zero_supported_eq_zero X k
    rw [hai (a i), map_zero, smul_zero]
  · rfl

end HodgeLean.Foundations.QuotientDuality

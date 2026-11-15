import HodgeLean.Foundations.QuotientDuality.ProperCycleZeroDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingletonRestriction
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollectedLocalNormalization
import HodgeLean.Foundations.QuotientDuality.ProperCycleCancellation

/-! # Exact collection on an actual zero-dimensional ambient scheme -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- Finite rational collection retains exact supported normalization in dimension zero.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1; Hatcher, Algebraic Topology, section 3.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_dimension_collected_descent
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 0)
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ)
    (hcharts : ∀ i, ∀ ξ ∈ (γ i).support, ∃ (r : ℕ)
      (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin 0 → ℂ)))
      (hS : ∀ z ∈ e.source, z ∈ a3b4_cycleSupport X.hom (γ i) ↔ (e z).2 = 0),
      a3b4_IsHolChart X.hom e ∧ ∃ z : ComplexPoint X,
        z ∈ e.source ∧ z ∈ a3b4_cycleSupport X.hom (γ i) ∧
        Point.underlying z ∈ closure {ξ} ∧
        ∀ ζ ∈ (γ i).support, Point.underlying z ∈ closure {ζ} → ζ = ξ)
    (a : ∀ i, s2e_supportedClass X (γ i) 0)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) 0 (a i)) (q : I → ℚ) :
    let Γ : AlgebraicCycle X.left ℚ := ∑ i, (γ i).mapRange (q i * ·) (mul_zero _)
    let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
    let hT : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T :=
      fun i hi z hz => Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩
    ∃ s : s2e_supportedClass X Γ 0, a3b4_IsCycleClass X.hom Γ 0 s ∧
      enlargeSupport ℚ (a3b4_an X.hom) (properCycle_collected_support_subset X γ q) 0 s =
        SupportedClasses.weightedSum (a3b4_an X.hom) 0
          (fun i => a3b4_cycleSupport X.hom (γ i)) T q hT a := by
  classical
  dsimp only
  letI : Subsingleton (a3b4_an X.hom) := properCycle_zero_dimension_complex_subsingleton X hdim
  letI : Subsingleton (ComplexPoint X) := properCycle_zero_dimension_complex_subsingleton X hdim
  let Γ : AlgebraicCycle X.left ℚ := ∑ i, (γ i).mapRange (q i * ·) (mul_zero _)
  let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
  let hT : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T :=
    fun i hi z hz => Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩
  let w := SupportedClasses.weightedSum (a3b4_an X.hom) 0
    (fun i => a3b4_cycleSupport X.hom (γ i)) T q hT a
  have hother (ξ : X.left) : ∀ i η, η ∈ (γ i).support → η ≠ ξ →
      ∀ z : ComplexPoint X, z.underlying ∉ closure ({η} : Set X.left) := by
    intro i η _ hn z _
    exact hn ((properCycle_zero_dimension_point_eq_generic X hdim η).trans
      (properCycle_zero_dimension_point_eq_generic X hdim ξ).symm)
  by_cases hΓ : Γ = 0
  · by_cases hzero : ∀ i, q i = 0 ∨ γ i = 0
    · exact properCycle_inactive_terms_descent X 0 γ a q hzero
    · push Not at hzero
      obtain ⟨i, hqi, hγi⟩ := hzero
      obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ ∈ (γ i).support := by
        by_contra hn
        apply hγi
        ext ξ
        exact not_ne_iff.mp (fun hh => hn ⟨ξ, hh⟩)
      obtain ⟨r, e, hS, he, z, hz, hzS, hzξ, _⟩ := hcharts i ξ hξ
      have hwhole : T = Set.univ := Set.eq_univ_of_forall (fun y =>
        hT i hqi (by rw [properCycle_zero_dimension_nonzero_support X hdim (γ i) hγi]; trivial))
      have heT : ∀ y ∈ e.source, y ∈ T ↔ (e y).2 = 0 := by
        intro y hy
        rw [hwhole]
        simp only [Set.mem_univ, true_iff]
        exact Subsingleton.elim _ _
      have hp : ∀ y ∈ e.source, y.underlying ∈ closure ({ξ} : Set X.left) ↔ (e y).2 = 0 := by
        intro y hy
        have hyz : y = z := Subsingleton.elim _ _
        subst y
        exact iff_of_true hzξ (Subsingleton.elim _ _)
      obtain ⟨W, hzW, hWe, hW⟩ := properCycle_weighted_isolated_component_cancellation
        X 0 γ a ha q T hT r e heT he z hz ξ hzξ hp
        (fun i η hm hn => hother ξ i η hm hn z)
        (by change Γ ξ = 0; rw [hΓ]; rfl)
      have hw : w = 0 := properCycle_subsingleton_neighborhood_restriction_injective
        (a3b4_an X.hom) T (W : Set (ComplexPoint X)) z hzW 0 (hW.trans (map_zero _).symm)
      have hn : a3b4_IsCycleClass X.hom Γ 0 0 := by
        rw [hΓ]; exact properCycle_zero_normalized X 0
      exact ⟨0, hn, (map_zero _).trans hw.symm⟩
  · have hS := properCycle_zero_dimension_nonzero_support X hdim Γ hΓ
    have hST := properCycle_collected_support_subset X γ q
    have heq : a3b4_cycleSupport X.hom Γ = T := by
      apply Set.Subset.antisymm hST
      rw [hS]
      exact Set.subset_univ _
    obtain ⟨s, hs⟩ := properCycle_equal_support_enlargement_surjective
      (a3b4_an X.hom) _ T hST heq 0 w
    refine ⟨s, ?_, hs⟩
    intro r e heS z hz hzS he
    let ξ := genericPoint X.left
    have hzξ : z.underlying ∈ closure ({ξ} : Set X.left) := by
      apply specializes_iff_mem_closure.mp
      apply Scheme.le_iff_specializes.mp
      exact le_top
    obtain ⟨W, hWe, hzW, hW⟩ := properCycle_collected_lift_normalization_at_isolated_point
      X 0 γ q a ha s hs r e heS he z hz hzS ξ hzξ
      (fun i η hm hn => hother ξ i η hm hn z)
    exact ⟨(W : Set (ComplexPoint X)), hWe, W.isOpen, hzW, hW⟩

end HodgeLean.Foundations.QuotientDuality

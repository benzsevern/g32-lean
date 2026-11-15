import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportSumInjective
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportEnlargement
import HodgeLean.Foundations.QuotientDuality.ProperCycleCoordinateInclusion
import HodgeLean.Foundations.QuotientDuality.ProperCyclePureSupportInclusion

/-! # Intrinsic support sums and literal zero extension
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual homology inclusion carries the intrinsic source sum to the target sum with precisely the zero-extended prime coefficients.
Source: Fulton, Intersection Theory, sections 1.5 and 19.1; properCycle_intrinsic_component_on_support_enlarge.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_support_sum_enlarge
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ δ : AlgebraicCycle X.left ℚ)
    (hcγ : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (hcδ : ∀ ξ ∈ δ.support, Order.coheight ξ = k)
    (h : a3b4_cycleSupport X.hom γ ⊆ a3b4_cycleSupport X.hom δ)
    (v : γ.support → ℚ) :
    homologyMap ℚ (2*k) (TopCat.ofHom (ContinuousMap.inclusion h))
      (properCycle_intrinsic_support_sum X k hdim γ hcγ v) =
      properCycle_intrinsic_support_sum X k hdim δ hcδ
        (properCycle_include_coordinates X.left γ δ v) := by
  classical
  have hprimes := properCycle_pure_prime_support_subset X k γ δ hcγ hcδ h
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : Fintype γ.support := (a3b2_support_finite γ).fintype
  letI : Fintype δ.support := (a3b2_support_finite δ).fintype
  let C (ξ : δ.support) := properCycle_intrinsic_component_on_support X δ ξ.val ξ.property k
    (properCycle_middle_component_dimension X k hdim ξ.val (hcδ ξ.val ξ.property))
  change homologyMap ℚ (2*k) (TopCat.ofHom (ContinuousMap.inclusion h))
    (∑ ξ : γ.support, v ξ • properCycle_intrinsic_component_on_support X γ ξ.val ξ.property k
      (properCycle_middle_component_dimension X k hdim ξ.val (hcγ ξ.val ξ.property))) =
    ∑ ξ : δ.support, properCycle_extend_coordinates X.left γ v ξ.val • C ξ
  rw [map_sum]
  simp only [map_smul]
  let i : γ.support → δ.support := fun ξ => ⟨ξ.val, hprimes ξ.property⟩
  trans ∑ ξ : γ.support, v ξ • C (i ξ)
  · apply Finset.sum_congr rfl
    intro ξ _
    exact congrArg (fun t => v ξ • t)
      (properCycle_intrinsic_component_on_support_enlarge X γ δ h ξ.val ξ.property
        (hprimes ξ.property) k
        (properCycle_middle_component_dimension X k hdim ξ.val (hcγ ξ.val ξ.property)))
  · apply Finset.sum_bij_ne_zero (fun ξ _ _ => i ξ)
    · intro ξ _ _
      exact Finset.mem_univ _
    · intro ξ _ _ η _ _ he
      exact Subtype.ext (congrArg (fun z : δ.support => z.val) he)
    · intro η _ hn
      have hη : η.val ∈ γ.support := by
        by_contra hh
        apply hn
        change (if hγ : η.val ∈ γ.support then v ⟨η.val, hγ⟩ else 0) • C η = 0
        rw [dif_neg hh, zero_smul]
      let ξ : γ.support := ⟨η.val, hη⟩
      have he : i ξ = η := Subtype.ext rfl
      have hv : properCycle_extend_coordinates X.left γ v η.val = v ξ := by
        change (if hγ : η.val ∈ γ.support then v ⟨η.val, hγ⟩ else 0) = v ξ
        rw [dif_pos hη]
      refine ⟨ξ, Finset.mem_univ _, ?_, he⟩
      intro hz
      apply hn
      rw [hv, ← he]
      exact hz
    · intro ξ _ _
      change v ξ • C (i ξ) =
        (if hγ : ξ.val ∈ γ.support then v ⟨ξ.val, hγ⟩ else 0) • C (i ξ)
      rw [dif_pos ξ.property]

/-- Actual support inclusion cannot annihilate a nonzero intrinsic coefficient combination on a pure source support.
Source: properCycle_intrinsic_support_sum_enlarge; properCycle_intrinsic_support_sum_injective.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_support_sum_enlarge_injective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ δ : AlgebraicCycle X.left ℚ)
    (hcγ : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (hcδ : ∀ ξ ∈ δ.support, Order.coheight ξ = k)
    (h : a3b4_cycleSupport X.hom γ ⊆ a3b4_cycleSupport X.hom δ) :
    Function.Injective ((homologyMap ℚ (2*k) (TopCat.ofHom (ContinuousMap.inclusion h))).comp
      (properCycle_intrinsic_support_sum X k hdim γ hcγ)) := by
  intro v w he
  apply properCycle_include_coordinates_injective X.left γ δ
    (properCycle_pure_prime_support_subset X k γ δ hcγ hcδ h)
  apply properCycle_intrinsic_support_sum_injective X k hdim δ hcδ
  change homologyMap ℚ (2*k) (TopCat.ofHom (ContinuousMap.inclusion h))
    (properCycle_intrinsic_support_sum X k hdim γ hcγ v) =
    homologyMap ℚ (2*k) (TopCat.ofHom (ContinuousMap.inclusion h))
      (properCycle_intrinsic_support_sum X k hdim γ hcγ w) at he
  rw [properCycle_intrinsic_support_sum_enlarge X k hdim γ δ hcγ hcδ h v,
    properCycle_intrinsic_support_sum_enlarge X k hdim γ δ hcγ hcδ h w] at he
  exact he

end HodgeLean.Foundations.QuotientDuality

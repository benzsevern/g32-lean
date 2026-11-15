import HodgeLean.Foundations.QuotientDuality.RetainedCyclePureEnlargement
import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionCycle

/-! Detection of the active carrier inside the full family carrier. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Classical
namespace HodgeLean.Foundations.QuotientDuality

/-- The active-to-full enlargement is injective for finite pure middle cycle families. -/
lemma retained_active_to_full_injective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (hc : ∀ i ξ, ξ ∈ (γ i).support → Order.coheight ξ = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*k+2*k) c x))
    (hv : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    (h : (⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)) ⊆
      ⋃ i, a3b4_cycleSupport X.hom (γ i)) :
    Function.Injective (enlargeSupport ℚ (a3b4_an X.hom) h (2*k)) := by
  let δ := properCycle_unsigned_family γ q
  let τ := properCycle_unsigned_family γ (fun _ => (1 : ℚ))
  have hcδ : ∀ ξ ∈ δ.support, Order.coheight ξ = k := by
    intro ξ hξ
    obtain ⟨i, _, hi⟩ := (properCycle_unsigned_family_support γ q ξ).mp hξ
    exact hc i ξ hi
  have hcτ : ∀ ξ ∈ τ.support, Order.coheight ξ = k := by
    intro ξ hξ
    obtain ⟨i, _, hi⟩ :=
      (properCycle_unsigned_family_support γ (fun _ => (1 : ℚ)) ξ).mp hξ
    exact hc i ξ hi
  have heδ := properCycle_unsigned_family_analytic_support X γ q
  have heτ : a3b4_cycleSupport X.hom τ = ⋃ i, a3b4_cycleSupport X.hom (γ i) := by
    rw [properCycle_unsigned_family_analytic_support]
    ext z
    constructor
    · intro hz
      obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp hz
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion₂.mpr ⟨i, one_ne_zero, hi⟩
  have hi : ∀ h : a3b4_cycleSupport X.hom δ ⊆ a3b4_cycleSupport X.hom τ,
      Function.Injective (enlargeSupport ℚ (a3b4_an X.hom) h (2*k)) := by
    intro h
    exact retained_pure_support_enlarge_injective X k hk hdim δ τ hcδ hcτ h c ho hv
  change a3b4_cycleSupport X.hom δ = _ at heδ
  rw [heδ, heτ] at hi
  exact hi h

end HodgeLean.Foundations.QuotientDuality

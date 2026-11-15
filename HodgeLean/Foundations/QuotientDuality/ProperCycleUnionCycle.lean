import HodgeLean.Foundations.QuotientDuality.ProperCycleCollection

/-! # A positive rational cycle retaining the actual active union support -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- The finite sum of absolute weighted coefficients retains each active component.
Source: Fulton, Intersection Theory, section 1.5, effective rational cycles and finite supports.
HC no distance; AV milestone no distance. -/
def properCycle_unsigned_family {X : Scheme.{0}} {I : Type} [Fintype I]
    (γ : I → AlgebraicCycle X ℚ) (q : I → ℚ) : AlgebraicCycle X ℚ :=
  ∑ i, (γ i).mapRange (fun c => |q i * c|) (by simp)

/-- The positive family cycle has exactly the components occurring in active terms.
Source: Fulton, Intersection Theory, section 1.5, effective rational cycles and finite supports.
HC no distance; AV milestone no distance. -/
lemma properCycle_unsigned_family_support {X : Scheme.{0}} {I : Type} [Fintype I]
    (γ : I → AlgebraicCycle X ℚ) (q : I → ℚ) (ξ : X) :
    ξ ∈ (properCycle_unsigned_family γ q).support ↔
      ∃ i, q i ≠ 0 ∧ ξ ∈ (γ i).support := by
  classical
  change (properCycle_unsigned_family γ q) ξ ≠ 0 ↔ ∃ i, q i ≠ 0 ∧ γ i ξ ≠ 0
  have hev : (properCycle_unsigned_family γ q) ξ = ∑ i, |q i * γ i ξ| := by
    simp only [properCycle_unsigned_family, Function.locallyFinsuppWithin.coe_sum,
      Finset.sum_apply, Function.locallyFinsuppWithin.mapRange_apply]
  rw [hev]
  constructor
  · intro hn
    by_contra hh
    apply hn
    apply Finset.sum_eq_zero
    intro i _
    have h := not_exists.mp hh i
    by_cases hi : q i = 0
    · simp [hi]
    · have hγ : γ i ξ = 0 := by simpa [hi] using h
      simp [hγ]
  · rintro ⟨i, hi, hξ⟩
    have hp : 0 < |q i * γ i ξ| := abs_pos.mpr (mul_ne_zero hi hξ)
    have hs : |q i * γ i ξ| ≤ ∑ j, |q j * γ j ξ| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (q j * γ j ξ)) (Finset.mem_univ i)
    exact ne_of_gt (hp.trans_le hs)

/-- The actual analytic support of the positive family cycle is the active union used in finite weighted enlargement.
Source: Fulton, Intersection Theory, section 1.5, supports of effective rational cycles.
HC no distance; AV milestone no distance. -/
lemma properCycle_unsigned_family_analytic_support
    (X : CategoryTheory.Over (Spec ↧ℂ)) [IsProjective X.hom]
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ) :
    a3b4_cycleSupport X.hom (properCycle_unsigned_family γ q) =
      ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨ξ, hξ, hxξ⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨i, hi, hξi⟩ := (properCycle_unsigned_family_support γ q ξ).mp hξ
    exact Set.mem_iUnion₂.mpr ⟨i, hi, Set.mem_iUnion₂.mpr ⟨ξ, hξi, hxξ⟩⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨ξ, hξ, hxξ⟩ := Set.mem_iUnion₂.mp hxi
    exact Set.mem_iUnion₂.mpr ⟨ξ, (properCycle_unsigned_family_support γ q ξ).mpr ⟨i, hi, hξ⟩, hxξ⟩

/-- Every component of the positive family cycle retains the original component codimension bound.
Source: Fulton, Intersection Theory, section 1.5, finite cycle supports.
HC no distance; AV milestone no distance. -/
lemma properCycle_unsigned_family_coheight
    {X : Scheme.{0}} {I : Type} [Fintype I]
    (γ : I → AlgebraicCycle X ℚ) (q : I → ℚ) (k : ℕ)
    (hcodim : ∀ i ξ, ξ ∈ (γ i).support → (k : ℕ∞) ≤ Order.coheight ξ) :
    ∀ ξ ∈ (properCycle_unsigned_family γ q).support, (k : ℕ∞) ≤ Order.coheight ξ := by
  intro ξ hξ
  obtain ⟨i, _, hi⟩ := (properCycle_unsigned_family_support γ q ξ).mp hξ
  exact hcodim i ξ hi

end HodgeLean.Foundations.QuotientDuality

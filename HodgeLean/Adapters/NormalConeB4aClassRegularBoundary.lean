import HodgeLean.Adapters.NormalConeB4aClassBoundary
import HodgeLean.Adapters.NormalConeB4aClassCycleExtension

/-! # A finite boundary for the regular codimension locus

Remove each component's singular remainder, every component of higher
codimension, and pairwise intersections. The remaining support lies on one
smooth component of the specified codimension at each point.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- The finite algebraic boundary used to separate regular codimension-`c`
components. Source: Fulton, *Intersection Theory*, second edition, §19.1. -/
def a3b4a_classRegularBoundary
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] (γ : AlgebraicCycle Z ℚ) (c : ℕ) : Closeds Z := by
  classical
  letI : CompactSpace Z := a3b4_compactSpace q
  let s := (a3b2_support_finite γ).toFinset
  let C : Z → Closeds Z := fun x => ⟨closure {x}, isClosed_closure⟩
  exact s.sup fun x => reducedClosedSingularRemainder q (C x) ⊔
    (if ((c + 1 : ℕ) : ℕ∞) ≤ Order.coheight x then C x else ⊥) ⊔
    s.sup (fun y => if x = y then ⊥ else C x ⊓ C y)

/-- The regular-locus boundary is contained in the original algebraic support. -/
theorem a3b4a_classRegularBoundary_le
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] (γ : AlgebraicCycle Z ℚ) (c : ℕ) :
    a3b4a_classRegularBoundary q γ c ≤ a3b4a_classAlgebraicSupport q γ := by
  classical
  letI : CompactSpace Z := a3b4_compactSpace q
  unfold a3b4a_classRegularBoundary
  apply Finset.sup_le
  intro x hx
  have hxγ : x ∈ γ.support := (a3b2_support_finite γ).mem_toFinset.mp hx
  have hC : (⟨closure {x}, isClosed_closure⟩ : Closeds Z) ≤ a3b4a_classAlgebraicSupport q γ := by
    intro z hz
    exact Set.mem_iUnion₂.mpr ⟨x, hxγ, hz⟩
  apply sup_le
  · apply sup_le ((reducedClosedSingularRemainder_le q _).trans hC)
    split_ifs
    · exact hC
    · exact bot_le
  · apply Finset.sup_le
    intro y hy
    split_ifs
    · exact bot_le
    · exact inf_le_left.trans hC

/-- Membership in the finite boundary records a singular point, a component
of higher codimension, or an intersection of distinct components. -/
theorem a3b4a_classRegularBoundary_mem
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] (γ : AlgebraicCycle Z ℚ) (c : ℕ) (z : Z) :
    z ∈ a3b4a_classRegularBoundary q γ c ↔ ∃ x ∈ γ.support,
      z ∈ reducedClosedSingularRemainder q ⟨closure {x}, isClosed_closure⟩ ∨
      (((c + 1 : ℕ) : ℕ∞) ≤ Order.coheight x ∧ z ∈ closure ({x} : Set Z)) ∨
      ∃ y ∈ γ.support, x ≠ y ∧ z ∈ closure ({x} : Set Z) ∧ z ∈ closure ({y} : Set Z) := by
  classical
  letI : CompactSpace Z := a3b4_compactSpace q
  have hsup (s : Finset Z) (F : Z → Closeds Z) :
      z ∈ s.sup F ↔ ∃ x ∈ s, z ∈ F x := by
    change z ∈ (↑(s.sup F) : Set Z) ↔ _
    rw [Closeds.coe_finset_sup, Finset.sup_eq_iSup]
    simp
  have hunion (A B : Closeds Z) : z ∈ A ⊔ B ↔ z ∈ A ∨ z ∈ B := Iff.rfl
  have hinter (A B : Closeds Z) : z ∈ A ⊓ B ↔ z ∈ A ∧ z ∈ B := Iff.rfl
  have hite (p : Prop) (A B : Closeds Z) :
      z ∈ (if p then A else B) ↔ (p ∧ z ∈ A) ∨ (¬p ∧ z ∈ B) := by
    by_cases h : p <;> simp [h]
  simp only [a3b4a_classRegularBoundary, hsup, hunion, hinter, hite]
  simp only [Set.Finite.mem_toFinset, show z ∈ (⊥ : Closeds Z) ↔ False from Iff.rfl,
    and_false, or_false, false_or, or_assoc]
  apply exists_congr
  intro x
  by_cases h : (c : ℕ∞) + 1 ≤ Order.coheight x <;>
    simp [h, show z ∈ (⊥ : Closeds Z) ↔ False from Iff.rfl]

end HodgeLean.Adapters

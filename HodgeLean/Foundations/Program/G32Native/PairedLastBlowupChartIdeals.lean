import Mathlib.RingTheory.Ideal.Operations

/-! # Ideal identities in the two charts of the last paired blowup -/

namespace HodgeLean.Foundations.Program.G32Native

/-- In the chart `t = s*v`, cancellation modulo the strict component
identifies the total transform with the scheme-theoretic union.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13,
affine blowup charts; Schoen, Compositio Mathematica 65 (1988),
Sublemma 2.7, pp. 16–17. -/
theorem paired_last_chart_union {R : Type*} [CommRing R]
    (K : Ideal R) (s v : R)
    (hreg : ∀ x : R, s * x ∈ K ⊔ Ideal.span {v} →
      x ∈ K ⊔ Ideal.span {v}) :
    (K ⊔ Ideal.span {v}) ⊓ (K ⊔ Ideal.span {s}) =
      K ⊔ Ideal.span {s * v} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx.2
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
    have hsc : s * c ∈ K ⊔ Ideal.span {v} := by
      have h := (K ⊔ Ideal.span {v}).sub_mem hx.1 (Submodule.mem_sup_left ha)
      simpa only [← hab, add_sub_cancel_left] using h
    obtain ⟨d, hd, e, he, hde⟩ := Submodule.mem_sup.mp (hreg c hsc)
    obtain ⟨f, rfl⟩ := Ideal.mem_span_singleton.mp he
    apply Submodule.mem_sup.mpr
    refine ⟨a + s * d, K.add_mem ha (K.mul_mem_left s hd), (s * v) * f, ?_, ?_⟩
    · exact Ideal.mem_span_singleton.mpr ⟨f, rfl⟩
    · rw [← hab, ← hde]
      ring
  · apply le_inf
    · apply sup_le le_sup_left
      apply Ideal.span_le.mpr
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton v)))
    · apply sup_le le_sup_left
      apply Ideal.span_le.mpr
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact Submodule.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton s)))

/-- The exceptional ideal plus the total transform is the residual ideal
in the first chart, with the transverse equations retained.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem paired_last_chart_residual {R : Type*} [CommRing R]
    (K : Ideal R) (s v : R) :
    Ideal.span {s} ⊔ (K ⊔ Ideal.span {s * v}) = K ⊔ Ideal.span {s} := by
  apply le_antisymm
  · apply sup_le le_sup_right
    apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Submodule.mem_sup_right
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton s)))
  · exact sup_le (le_sup_of_le_right le_sup_left) le_sup_left

/-- In the second chart `s = t*w`, the strict component is empty and
the residual ideal is already the total-transform ideal.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem paired_last_second_chart {R : Type*} [CommRing R]
    (K : Ideal R) (t : R) :
    (⊤ : Ideal R) ⊓ (K ⊔ Ideal.span {t}) = K ⊔ Ideal.span {t} ∧
      Ideal.span {t} ⊔ (K ⊔ Ideal.span {t}) = K ⊔ Ideal.span {t} := by
  exact ⟨top_inf_eq _, sup_eq_right.mpr le_sup_right⟩

#print axioms paired_last_chart_union
#print axioms paired_last_chart_residual
#print axioms paired_last_second_chart

end HodgeLean.Foundations.Program.G32Native

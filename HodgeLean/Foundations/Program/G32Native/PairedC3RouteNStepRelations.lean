import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

/-! # Relations on the exceptional conormal generator in an adapted chart -/
namespace HodgeLean.Foundations.Program.G32Native
variable {B : Type*} [CommRing B]

/-- Killing the total transform and the square of the strict-transform
ideal leaves precisely the two relations on the exceptional direction. -/
theorem paired_c3_chart_relation_ideal (K : Ideal B) (s v : B) :
    (K ⊔ Ideal.span {s * v}) ⊔ (K ⊔ Ideal.span {v}) ^ 2 =
      K ⊔ Ideal.span {s * v, v ^ 2} := by
  apply le_antisymm
  · refine sup_le (sup_le le_sup_left ?_) ?_
    · apply Ideal.span_le.mpr
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact Submodule.mem_sup_right (Ideal.subset_span (by simp only [Set.mem_insert_iff, true_or, Set.mem_singleton_iff]))
    · rw [pow_two, Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
      refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · exact le_trans Ideal.mul_le_left le_sup_left
      · exact le_trans Ideal.mul_le_left le_sup_left
      · exact le_trans Ideal.mul_le_right le_sup_left
      · rw [Ideal.span_singleton_mul_span_singleton]
        apply Ideal.span_le.mpr
        intro x hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact Submodule.mem_sup_right (Ideal.subset_span (by simp only [pow_two, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]))
  · refine sup_le (le_trans le_sup_left le_sup_left) ?_
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
    · rcases Set.mem_singleton_iff.mp hx with rfl
      apply Submodule.mem_sup_right
      simp only [pow_two]
      exact Ideal.mul_mem_mul (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
        (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))

/-- Regularity of the exceptional direction modulo the transverse
ideal computes all relations on its class, including the square relation. -/
theorem paired_c3_chart_generator_relations (K : Ideal B) (s v a : B)
    (hv : ∀ b : B, v * b ∈ K → b ∈ K) :
    a * v ∈ (K ⊔ Ideal.span {s * v}) ⊔ (K ⊔ Ideal.span {v}) ^ 2 ↔
      a ∈ K ⊔ Ideal.span {s, v} := by
  rw [paired_c3_chart_relation_ideal]
  constructor
  · intro ha
    obtain ⟨k, hk, w, hw, he⟩ := Submodule.mem_sup.mp ha
    obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.mp hw
    have hm : v * (a - (b * s + c * v)) ∈ K := by
      have he' : v * (a - (b * s + c * v)) = k := by
        calc
          v * (a - (b * s + c * v)) = a * v - (b * (s * v) + c * v ^ 2) := by ring
          _ = k := by rw [← he]; ring
      rwa [he']
    have ha' := hv _ hm
    have hb : b * s + c * v ∈ Ideal.span {s, v} :=
      Ideal.mem_span_pair.mpr ⟨b, c, rfl⟩
    have hsum := (K ⊔ Ideal.span {s, v}).add_mem
      (Submodule.mem_sup_left ha') (Submodule.mem_sup_right hb)
    simpa only [sub_add_cancel] using hsum
  · intro ha
    obtain ⟨k, hk, w, hw, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.mp hw
    apply Submodule.mem_sup.mpr
    refine ⟨k * v, K.mul_mem_right v hk, b * (s * v) + c * v ^ 2,
      Ideal.mem_span_pair.mpr ⟨b, c, rfl⟩, ?_⟩
    ring

end HodgeLean.Foundations.Program.G32Native

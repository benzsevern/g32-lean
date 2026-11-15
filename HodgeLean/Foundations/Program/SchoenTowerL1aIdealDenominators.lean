import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Ring

/-! # Spreading finite ideal comparisons from a localization

A comparison for a finitely generated actual ideal is witnessed by one common
denominator in the original ring. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A localized inclusion of a finitely generated ideal has one denominator witnessing the original ideal inclusion.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3, localization of finitely generated ideals. -/
theorem s2v_l1a_finite_ideal_localization_denominator
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A] (I J : Ideal R) (hI : I.FG)
    (h : I.map (algebraMap R A) ≤ J.map (algebraMap R A)) :
    ∃ s ∈ M, ∀ x ∈ I, s * x ∈ J := by
  induction I, hI using Submodule.fg_induction with
  | singleton x =>
    have hx : algebraMap R A x ∈ J.map (algebraMap R A) :=
      h (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton x)))
    obtain ⟨s, hs, hsx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M A J x).mp hx
    refine ⟨s, hs, ?_⟩
    intro r hr
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hr
    rw [← mul_assoc]
    exact J.mul_mem_right a hsx
  | sup I K hI hK ihI ihK =>
    obtain ⟨s, hs, hIs⟩ := ihI ((Ideal.map_mono le_sup_left).trans h)
    obtain ⟨t, ht, hKt⟩ := ihK ((Ideal.map_mono le_sup_right).trans h)
    refine ⟨s * t, M.mul_mem hs ht, ?_⟩
    intro r hr
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hr
    have heq : s * t * (x + y) = t * (s * x) + s * (t * y) := by ring
    rw [heq]
    exact J.add_mem (J.mul_mem_left t (hIs x hx)) (J.mul_mem_left s (hKt y hy))

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNStepRelations
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monic

/-! # Generator relations surviving a quotient chart presentation -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native
open Polynomial

/-- A translated polynomial variable cancels modulo every coefficient ideal.
No regularity or primality of the coefficient ideal is required. -/
theorem paired_c3_translated_variable_cancel
    {A : Type*} [CommRing A] (I : Ideal A) (a : A) (p : A[X])
    (hp : (X - C a) * p ∈ I.map C) : p ∈ I.map C := by
  have hk : RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk I)) = I.map C := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  rw [← hk, RingHom.mem_ker] at hp ⊢
  have hm : (X - C (Ideal.Quotient.mk I a)) * p.map (Ideal.Quotient.mk I) = 0 := by
    simpa only [coe_mapRingHom, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C] using hp
  apply (monic_X_sub_C (Ideal.Quotient.mk I a)).isRegular.left
  simpa only [coe_mapRingHom, mul_zero] using hm

/-- The relation calculation for the distinguished conormal generator
passes through any surjective chart map whose kernel lies in the total ideal. -/
theorem paired_c3_surjective_chart_generator_relations
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (K : Ideal A) (s w : A)
    (hw : ∀ a : A, w * a ∈ K → a ∈ K)
    (hker : RingHom.ker f ≤ K ⊔ Ideal.span {s * w}) (b : B) :
    b * f w ∈ (K ⊔ Ideal.span {s * w}).map f ⊔
        ((K ⊔ Ideal.span {w}).map f) ^ 2 ↔
      b ∈ (K ⊔ Ideal.span {s, w}).map f := by
  obtain ⟨p, rfl⟩ := hf b
  have hbig : RingHom.ker f ≤
      (K ⊔ Ideal.span {s * w}) ⊔ (K ⊔ Ideal.span {w}) ^ 2 :=
    le_trans hker le_sup_left
  have hsmall : RingHom.ker f ≤ K ⊔ Ideal.span {s, w} := by
    refine le_trans hker (sup_le le_sup_left ?_)
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    apply Submodule.mem_sup_right
    exact (Ideal.span {s, w}).mul_mem_left s
      (Ideal.subset_span (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]))
  have h₁ : f (p * w) ∈
      ((K ⊔ Ideal.span {s * w}) ⊔ (K ⊔ Ideal.span {w}) ^ 2).map f ↔
      p * w ∈ (K ⊔ Ideal.span {s * w}) ⊔ (K ⊔ Ideal.span {w}) ^ 2 := by
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' f hf, sup_eq_left.mpr hbig]
  have h₂ : f p ∈ (K ⊔ Ideal.span {s, w}).map f ↔
      p ∈ K ⊔ Ideal.span {s, w} := by
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' f hf, sup_eq_left.mpr hsmall]
  rw [← map_mul, ← Ideal.map_pow, ← Ideal.map_sup]
  exact h₁.trans ((paired_c3_chart_generator_relations K s w p hw).trans h₂.symm)

end HodgeLean.Foundations.Program.G32Native

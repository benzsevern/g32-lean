import HodgeLean.Foundations.Program.G32Native.PairedC3ChartRetraction

/-! # The direct ideal calculation in a retained Rees chart -/
noncomputable section
set_option maxHeartbeats 200000
open Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- The entire pulled-back slice ideal is the intersection of the
translated-ratio ideal with the residual ideal. The coefficient of the
ratio remains arbitrary.
Source: Hartshorne, Algebraic Geometry, II.7.13;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_direct_chart_union
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (u v a : A) (t : B) (I : Ideal A)
    (hs : Function.Surjective (eval₂RingHom f t))
    (hk : RingHom.ker (eval₂RingHom f t) = Ideal.span {C v - X * C u})
    (ha : v - a * u ∈ I)
    (hu : ∀ x : A, u * x ∈ I → x ∈ I) :
    I.map f = (I.map f ⊔ Ideal.span {t - f a}) ⊓
      (Ideal.span {f u} ⊔ I.map f) := by
  obtain ⟨g, hf, ht⟩ := paired_c3_chart_retraction f u v a t I hs hk ha
  have hker := paired_c3_chart_retraction_kernel f a t I hs g hf ht
  have hcancel := paired_c3_chart_kernel_cancel f u I g hf hu
  rw [hker] at hcancel
  have hrel : f v = t * f u := by
    have h : C v - X * C u ∈ RingHom.ker (eval₂RingHom f t) := by
      rw [hk]
      exact Ideal.subset_span (Set.mem_singleton _)
    change eval₂ f t (C v - X * C u) = 0 at h
    simpa only [eval₂_sub, eval₂_C, eval₂_mul, eval₂_X, sub_eq_zero] using h
  have hprod : f u * (t - f a) ∈ I.map f := by
    have h := Ideal.mem_map_of_mem f ha
    have heq : f u * (t - f a) = f (v - a * u) := by
      rw [map_sub, map_mul, hrel]
      ring
    rwa [heq]
  have hsup : I.map f ⊔ Ideal.span {f u * (t - f a)} = I.map f :=
    sup_eq_left.mpr (Ideal.span_le.mpr (by
      intro b hb
      obtain rfl := Set.mem_singleton_iff.mp hb
      exact hprod))
  rw [sup_comm (Ideal.span {f u})]
  rw [paired_last_chart_union (I.map f) (f u) (t - f a) hcancel, hsup]

#print axioms paired_c3_direct_chart_union
end HodgeLean.Foundations.Program.G32Native

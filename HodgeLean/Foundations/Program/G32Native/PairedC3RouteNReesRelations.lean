import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNQuotientChartRelations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Relations on the ratio class without transverse slice generators -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- The normalized ratio has exactly the reduced centre-slice relations
in an original Rees chart. The whole slice ideal is retained; no list of
adapted generators is an input.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_rees_generator_relations
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (u v a : A) (t : B) (I : Ideal A)
    (hs : Function.Surjective (eval₂RingHom f t))
    (hk : RingHom.ker (eval₂RingHom f t) = Ideal.span {C v - X * C u})
    (ha : v - a * u ∈ I) (b : B) :
    b * (t - f a) ∈ I.map f ⊔ (I.map f ⊔ Ideal.span {t - f a}) ^ 2 ↔
      b ∈ I.map f ⊔ Ideal.span {f u, t - f a} := by
  let F := eval₂RingHom f t
  let K : Ideal A[X] := I.map C
  let w : A[X] := X - C a
  have hcoeff : K.map F = I.map f := by
    rw [Ideal.map_map]
    change I.map (F.comp C) = I.map f
    congr 1
    ext x
    exact eval₂_C _ _
  have hFw : F w = t - f a := by simp only [F, w, coe_eval₂RingHom, eval₂_sub, eval₂_X, eval₂_C]
  have hFs : F (C u) = f u := eval₂_C _ _
  have hrel : f v = t * f u := by
    have hmem : C v - X * C u ∈ RingHom.ker F := by
      rw [hk]
      exact Ideal.subset_span (Set.mem_singleton _)
    change eval₂ f t (C v - X * C u) = 0 at hmem
    simpa only [eval₂_sub, eval₂_C, eval₂_mul, eval₂_X, sub_eq_zero] using hmem
  have hprod : f u * (t - f a) ∈ I.map f := by
    have he : f u * (t - f a) = f (v - a * u) := by
      rw [map_sub, map_mul, hrel]
      ring
    rw [he]
    exact Ideal.mem_map_of_mem f ha
  have htotal : (K ⊔ Ideal.span {C u * w}).map F = I.map f := by
    rw [Ideal.map_sup, hcoeff, Ideal.map_span, Set.image_singleton,
      map_mul, hFs, hFw]
    exact sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hprod))
  have hstrict : (K ⊔ Ideal.span {w}).map F = I.map f ⊔ Ideal.span {t - f a} := by
    rw [Ideal.map_sup, hcoeff, Ideal.map_span, Set.image_singleton, hFw]
  have hres : (K ⊔ Ideal.span {C u, w}).map F =
      I.map f ⊔ Ideal.span {f u, t - f a} := by
    rw [Ideal.map_sup, hcoeff, Ideal.map_span, Set.image_insert_eq,
      Set.image_singleton, hFs, hFw]
  have hker : RingHom.ker F ≤ K ⊔ Ideal.span {C u * w} := by
    rw [hk]
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    have he : C v - X * C u = C (v - a * u) - C u * w := by
      dsimp only [w]
      rw [map_sub, map_mul]
      ring
    rw [he]
    exact (K ⊔ Ideal.span {C u * w}).sub_mem
      (Submodule.mem_sup_left (Ideal.mem_map_of_mem C ha))
      (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  have h := paired_c3_surjective_chart_generator_relations F hs K (C u) w
    (paired_c3_translated_variable_cancel I a) hker b
  rwa [htotal, hstrict, hres, hFw] at h

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.PairedC3ReesEquationIso
import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupRegularSequence
import Mathlib.Algebra.Polynomial.Taylor

/-! # Changing the branch equation in a retained Rees chart

The coefficient map stays fixed when the first branch equation changes
from `u` to `u - a*v`. The ratio changes from `s` to `s - f a`.
-/
noncomputable section
set_option maxHeartbeats 200000
open Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- Translation of the ratio preserves evaluation of every polynomial.
Source: Hartshorne, Algebraic Geometry, II.7.13, affine blowup charts. -/
theorem paired_c3_adapted_eval
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (s : B) (a : A) (p : A[X]) :
    eval₂ f (s - f a) (taylor a p) = eval₂ f s p := by
  rw [taylor_apply, eval₂_comp]
  simp only [eval₂_add, eval₂_X, eval₂_C, sub_add_cancel]

/-- The exact polynomial kernel survives the change of branch generator.
Source: Hartshorne, Algebraic Geometry, II.7.13, affine blowup charts. -/
theorem paired_c3_adapted_kernel
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (u v a : A) (s : B)
    (hk : RingHom.ker (eval₂RingHom f s) = Ideal.span {C u - X * C v}) :
    RingHom.ker (eval₂RingHom f (s - f a)) =
      Ideal.span {C (u - a * v) - X * C v} := by
  let e := (taylorEquiv a).toRingEquiv
  have he : (eval₂RingHom f (s - f a)).comp e.toRingHom = eval₂RingHom f s := by
    apply RingHom.ext
    intro p
    exact paired_c3_adapted_eval f s a p
  have hc : (RingHom.ker (eval₂RingHom f (s - f a))).comap e.toRingHom =
      RingHom.ker (eval₂RingHom f s) := by
    rw [RingHom.comap_ker, he]
  have hm := congrArg (Ideal.map e.toRingHom) hc
  rw [Ideal.map_comap_of_surjective e.toRingHom e.surjective, hk,
    Ideal.map_span, Set.image_singleton] at hm
  rw [hm]
  congr 2
  change taylor a (C u - X * C v) = C (u - a * v) - X * C v
  simp only [taylor_apply, sub_comp, mul_comp, C_comp, X_comp, map_sub, map_mul]
  ring

#print axioms paired_c3_adapted_eval
#print axioms paired_c3_adapted_kernel

/-- Polynomial generators still cover the chart after translating the ratio.
Source: Hartshorne, Algebraic Geometry, II.7.13, affine blowup charts. -/
theorem paired_c3_adapted_surjective
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (s : B) (a : A)
    (hs : Function.Surjective (eval₂RingHom f s)) :
    Function.Surjective (eval₂RingHom f (s - f a)) := by
  intro b
  obtain ⟨p, hp⟩ := hs b
  exact ⟨taylor a p, (paired_c3_adapted_eval f s a p).trans hp⟩

#print axioms paired_c3_adapted_surjective
end HodgeLean.Foundations.Program.G32Native

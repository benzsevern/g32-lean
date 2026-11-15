import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Actual affine fibre squares from quotient ideals -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Extension of an ideal gives the actual categorical pushout of its quotient map. -/
theorem residual_quotient_isPushout
    {R S : CommRingCat.{0}} (f : R ⟶ S) (I : Ideal R) :
    IsPushout f (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap (I.map f.hom) f.hom Ideal.le_comap_map)) := by
  let q := Ideal.Quotient.mk (I.map f.hom)
  let g := Ideal.quotientMap (I.map f.hom) f.hom Ideal.le_comap_map
  have hsq : f ≫ CommRingCat.ofHom q = CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
      CommRingCat.ofHom g := by
    ext r
    rfl
  have hk (s : PushoutCocone f (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
      I.map f.hom ≤ RingHom.ker s.inl.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change s.inl.hom (f.hom r) = 0
    have h := congrArg (fun a : R ⟶ s.pt => a.hom r) s.condition
    change s.inl.hom (f.hom r) = s.inr.hom (Ideal.Quotient.mk I r) at h
    rw [h, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  let desc (s : PushoutCocone f (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    CommRingCat.ofHom (Ideal.Quotient.lift (I.map f.hom) s.inl.hom (hk s))
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hsq desc ?_ ?_ ?_)
  · intro s
    ext r
    rfl
  · intro s
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact congrArg (fun a : R ⟶ s.pt => a.hom r) s.condition
  · intro s m hl hr
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact congrArg (fun a : S ⟶ s.pt => a.hom r) hl

/-- The extended quotient defines the actual affine scheme fibre square. -/
theorem residual_quotient_isPullback
    {R S : CommRingCat.{0}} (f : R ⟶ S) (I : Ideal R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (I.map f.hom) f.hom Ideal.le_comap_map)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f.hom))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (Spec.map f) := by
  exact (residual_quotient_isPushout f I).op.map Scheme.Spec

#print axioms residual_quotient_isPullback
#print axioms residual_quotient_isPushout
end HodgeLean.Foundations.Program.G32Native

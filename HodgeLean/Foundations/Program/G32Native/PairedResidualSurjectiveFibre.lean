import HodgeLean.Foundations.Program.G32Native.PairedResidualQuotientFibre
import Mathlib.RingTheory.Polynomial.Ideal

/-! # Scheme fibre squares detected by actual affine kernels -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A commuting affine square with quotient sides is a pushout when the original kernels agree after extension. -/
theorem residual_surjective_isPushout
    {R S B Q : CommRingCat.{0}} (f : R ⟶ S) (p : R ⟶ B)
    (a : S ⟶ Q) (b : B ⟶ Q) (hsq : f ≫ a = p ≫ b)
    (hp : Function.Surjective p.hom) (ha : Function.Surjective a.hom)
    (hker : (RingHom.ker p.hom).map f.hom = RingHom.ker a.hom) :
    IsPushout f p a b := by
  have hk (s : PushoutCocone f p) : RingHom.ker a.hom ≤ RingHom.ker s.inl.hom := by
    rw [← hker, Ideal.map_le_iff_le_comap]
    intro r hr
    change s.inl.hom (f.hom r) = 0
    have h := congrArg (fun v : R ⟶ s.pt => v.hom r) s.condition
    change s.inl.hom (f.hom r) = s.inr.hom (p.hom r) at h
    rw [h, hr, map_zero]
  let desc (s : PushoutCocone f p) : Q ⟶ s.pt :=
    CommRingCat.ofHom (a.hom.liftOfSurjective ha ⟨s.inl.hom, hk s⟩)
  have hleft (s : PushoutCocone f p) : a ≫ desc s = s.inl := by
    apply CommRingCat.hom_ext
    exact RingHom.liftOfSurjective_comp a.hom ha _
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hsq desc hleft ?_ ?_)
  · intro s
    ext x
    obtain ⟨r, rfl⟩ := hp x
    have h := congrArg (fun v : R ⟶ Q => v.hom r) hsq
    change a.hom (f.hom r) = b.hom (p.hom r) at h
    change (desc s).hom (b.hom (p.hom r)) = s.inr.hom (p.hom r)
    rw [← h]
    exact (congrArg (fun v : S ⟶ s.pt => v.hom (f.hom r)) (hleft s)).trans
      (congrArg (fun v : R ⟶ s.pt => v.hom r) s.condition)
  · intro s m hl hr
    ext x
    obtain ⟨r, rfl⟩ := ha x
    exact (congrArg (fun v : S ⟶ s.pt => v.hom r) hl).trans
      (congrArg (fun v : S ⟶ s.pt => v.hom r) (hleft s)).symm

/-- A polynomial parameter has its actual origin fibre given by the quotient by that parameter. -/
theorem residual_polynomial_origin_isPullback
    (R S : Type) [CommRing R] [CommRing S] (c : R →+* S) (t : S) :
    let J := Ideal.span {t}
    let q := Ideal.Quotient.mk J
    IsPullback (Spec.map (CommRingCat.ofHom (q.comp c)))
      (Spec.map (CommRingCat.ofHom q))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom c t))) := by
  let J := Ideal.span {t}
  let q := Ideal.Quotient.mk J
  have hs : CommRingCat.ofHom (Polynomial.eval₂RingHom c t) ≫ CommRingCat.ofHom q =
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) ≫ CommRingCat.ofHom (q.comp c) := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · change q ((Polynomial.eval₂RingHom c t) Polynomial.X) =
        (q.comp c) ((Polynomial.evalRingHom (0 : R)) Polynomial.X)
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply,
        Polynomial.coe_evalRingHom, Polynomial.eval_X, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hk : (RingHom.ker (Polynomial.evalRingHom (0 : R))).map
      (Polynomial.eval₂RingHom c t) = RingHom.ker q := by
    rw [Ideal.mk_ker, Polynomial.ker_evalRingHom]
    simp only [map_zero, sub_zero, Ideal.map_span, Set.image_singleton,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rfl
  exact (residual_surjective_isPushout _ _ _ _ hs
    (Polynomial.eval_surjective 0) Ideal.Quotient.mk_surjective hk).op.map Scheme.Spec

#print axioms residual_polynomial_origin_isPullback
#print axioms residual_surjective_isPushout
end HodgeLean.Foundations.Program.G32Native

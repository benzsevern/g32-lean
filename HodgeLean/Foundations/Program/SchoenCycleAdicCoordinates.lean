import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Compatible finite coordinates and adic limits -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Evaluation of an adic element respects the quotient transition maps.
Source: Mathlib, AdicCompletion.Ideal.mk_eq_mk. -/
theorem s2e_adic_eval_factor
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on I R with
  | h x =>
    simpa only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk] using AdicCompletion.Ideal.mk_eq_mk I h x

#print axioms s2e_adic_eval_factor

/-- Compatible maps of all finite quotients induce a map of adic rings.
Source: Mathlib, AdicCompletion.liftRingHom. -/
def s2e_adic_coordinates_map
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    (e : ∀ n : ℕ, (R ⧸ I ^ n) →+* (S ⧸ J ^ n))
    (he : ∀ {m n : ℕ} (h : m ≤ n) x,
      Ideal.Quotient.factorPow J h (e n x) = e m (Ideal.Quotient.factorPow I h x)) :
    AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J
    (fun n => (e n).comp (AdicCompletion.evalₐ I n).toRingHom)
    (fun h => RingHom.ext fun x => by
      change Ideal.Quotient.factorPow J h (e _ (AdicCompletion.evalₐ I _ x)) =
        e _ (AdicCompletion.evalₐ I _ x)
      rw [he h, s2e_adic_eval_factor])

#print axioms s2e_adic_coordinates_map

/-- Compatible finite quotient equivalences give an equivalence of adic rings.
Source: Mathlib, AdicCompletion.liftRingHom and AdicCompletion.ext_evalₐ. -/
theorem s2e_adic_coordinates_equiv
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    (e : ∀ n : ℕ, (R ⧸ I ^ n) ≃+* (S ⧸ J ^ n))
    (he : ∀ {m n : ℕ} (h : m ≤ n) x,
      Ideal.Quotient.factorPow J h (e n x) = e m (Ideal.Quotient.factorPow I h x)) :
    ∃ E : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ n x, AdicCompletion.evalₐ J n (E x) = e n (AdicCompletion.evalₐ I n x) := by
  have hi : ∀ {m n : ℕ} (h : m ≤ n) x,
      Ideal.Quotient.factorPow I h ((e n).symm x) =
        (e m).symm (Ideal.Quotient.factorPow J h x) := by
    intro m n h x
    apply (e m).injective
    rw [RingEquiv.apply_symm_apply, ← he h, RingEquiv.apply_symm_apply]
  let f := s2e_adic_coordinates_map I J (fun n => (e n).toRingHom) he
  let g := s2e_adic_coordinates_map J I (fun n => (e n).symm.toRingHom) hi
  have hf : ∀ n x, AdicCompletion.evalₐ J n (f x) = e n (AdicCompletion.evalₐ I n x) := by
    intro n x
    refine AdicCompletion.evalₐ_liftRingHom J _ ?_ n x
    intro a b h
    apply RingHom.ext
    intro y
    change Ideal.Quotient.factorPow J h (e b (AdicCompletion.evalₐ I b y)) =
      e a (AdicCompletion.evalₐ I a y)
    rw [he h, s2e_adic_eval_factor]
  have hg : ∀ n x, AdicCompletion.evalₐ I n (g x) = (e n).symm (AdicCompletion.evalₐ J n x) := by
    intro n x
    refine AdicCompletion.evalₐ_liftRingHom I _ ?_ n x
    intro a b h
    apply RingHom.ext
    intro y
    change Ideal.Quotient.factorPow I h ((e b).symm (AdicCompletion.evalₐ J b y)) =
      (e a).symm (AdicCompletion.evalₐ J a y)
    rw [hi h, s2e_adic_eval_factor]
  refine ⟨{ f with invFun := g, left_inv := ?_, right_inv := ?_ }, hf⟩
  · intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n (g (f x)) = _
    rw [hg, hf, RingEquiv.symm_apply_apply]
  · intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ J n (f (g x)) = _
    rw [hf, hg, RingEquiv.apply_symm_apply]

#print axioms s2e_adic_coordinates_equiv
end HodgeLean.Foundations.Program

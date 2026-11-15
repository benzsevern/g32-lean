import HodgeLean.Foundations.Program.SchoenCycleAdicRingMaps
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Module adic limits and extension of the defining ideal -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The finite module quotient is the quotient by the corresponding power of
 the extended ideal, with scalars restricted to the base ring.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Mathlib, Ideal.smul_top_eq_map. -/
def s2e_adic_scalar_quotient_equiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (n : ℕ) :
    (S ⧸ (I ^ n • ⊤ : Submodule R S)) ≃ₗ[R]
      (S ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Ideal S)) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
    simp only [smul_eq_mul, Ideal.mul_top])).trans
      (Submodule.Quotient.restrictScalarsEquiv R _)

#print axioms s2e_adic_scalar_quotient_equiv

/-- The scalar comparison preserves the class of each element.
Source: Mathlib, Submodule.quotEquivOfEq_mk and
Submodule.Quotient.restrictScalarsEquiv_mk. -/
theorem s2e_adic_scalar_quotient_equiv_mk
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (n : ℕ) (s : S) :
    s2e_adic_scalar_quotient_equiv (S := S) I n (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk s := by
  simp only [s2e_adic_scalar_quotient_equiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, Submodule.Quotient.restrictScalarsEquiv_mk]

#print axioms s2e_adic_scalar_quotient_equiv_mk

/-- The scalar comparison commutes with the finite quotient transition maps.
Source: Mathlib, Submodule.factorPow. -/
theorem s2e_adic_scalar_quotient_equiv_transition
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) {m n : ℕ} (h : m ≤ n)
    (z : S ⧸ (I ^ n • ⊤ : Submodule R S)) :
    AdicCompletion.transitionMap (I.map (algebraMap R S)) S h
        (s2e_adic_scalar_quotient_equiv I n z) =
      s2e_adic_scalar_quotient_equiv I m (AdicCompletion.transitionMap I S h z) := by
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    simp only [s2e_adic_scalar_quotient_equiv_mk, AdicCompletion.transitionMap,
      Submodule.factorPow, Submodule.factor, Submodule.mapQ_apply,
      Submodule.liftQ_apply, Submodule.mkQ_apply, LinearMap.id_apply]

#print axioms s2e_adic_scalar_quotient_equiv_transition

/-- The module adic limit over the base ring is linearly equivalent to the
adic ring for the extended ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
the equivalence is induced by the identity on each finite quotient. -/
def s2e_adic_scalar_extension_equiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) :
    AdicCompletion I S ≃ₗ[R] AdicCompletion (I.map (algebraMap R S)) S where
  toFun x := ⟨fun n => s2e_adic_scalar_quotient_equiv I n (x.val n), by
    intro m n h
    rw [s2e_adic_scalar_quotient_equiv_transition, x.property h]⟩
  invFun y := ⟨fun n => (s2e_adic_scalar_quotient_equiv I n).symm (y.val n), by
    intro m n h
    apply (s2e_adic_scalar_quotient_equiv I m).injective
    rw [LinearEquiv.apply_symm_apply, ← s2e_adic_scalar_quotient_equiv_transition,
      LinearEquiv.apply_symm_apply, y.property h]⟩
  left_inv x := AdicCompletion.ext fun n =>
    (s2e_adic_scalar_quotient_equiv I n).symm_apply_apply (x.val n)
  right_inv y := AdicCompletion.ext fun n =>
    (s2e_adic_scalar_quotient_equiv I n).apply_symm_apply (y.val n)
  map_add' x y := AdicCompletion.ext fun n =>
    (s2e_adic_scalar_quotient_equiv I n).map_add (x.val n) (y.val n)
  map_smul' r x := AdicCompletion.ext fun n =>
    (s2e_adic_scalar_quotient_equiv I n).map_smul r (x.val n)

#print axioms s2e_adic_scalar_extension_equiv

/-- The module-to-ring adic equivalence preserves the image of each element.
Source: Mathlib, AdicCompletion.of; the finite quotient maps preserve representatives. -/
theorem s2e_adic_scalar_extension_equiv_of
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (s : S) :
    s2e_adic_scalar_extension_equiv I (AdicCompletion.of I S s) =
      AdicCompletion.of (I.map (algebraMap R S)) S s := by
  apply AdicCompletion.ext
  intro n
  exact s2e_adic_scalar_quotient_equiv_mk I n s

#print axioms s2e_adic_scalar_extension_equiv_of

/-- Transporting an induced adic endomorphism through the scalar equivalence
acts on original elements by the original linear map.
Source: Mathlib, AdicCompletion.map_of. -/
theorem s2e_adic_scalar_extension_map_of
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (f : S →ₗ[R] S) (s : S) :
    let e := s2e_adic_scalar_extension_equiv (S := S) I
    e (AdicCompletion.map I f
      (e.symm (AdicCompletion.of (I.map (algebraMap R S)) S s))) =
        AdicCompletion.of (I.map (algebraMap R S)) S (f s) := by
  dsimp only
  rw [← s2e_adic_scalar_extension_equiv_of, LinearEquiv.symm_apply_apply,
    AdicCompletion.map_of, s2e_adic_scalar_extension_equiv_of]

#print axioms s2e_adic_scalar_extension_map_of
/-- Scalar comparison intertwines an algebra endomorphism with its canonical
map on the extended-ideal adic ring.
Source: Mathlib, AdicCompletion.map_val_apply; finite quotient representatives. -/
theorem s2e_adic_scalar_extension_map
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (f : S →ₐ[R] S)
    (hf : (I.map (algebraMap R S)).map f.toRingHom ≤ I.map (algebraMap R S))
    (x : AdicCompletion I S) :
    s2e_adic_scalar_extension_equiv I (AdicCompletion.map I f.toLinearMap x) =
      s2e_adic_ring_map _ _ f.toRingHom hf (s2e_adic_scalar_extension_equiv I x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2e_adic_ring_map_eval]
  let J := I.map (algebraMap R S)
  have hJ : (J ^ n • ⊤ : Ideal S) ≤ J ^ n := by simp
  rw [← AdicCompletion.factor_eval_eq_evalₐ _ _ hJ,
    ← AdicCompletion.factor_eval_eq_evalₐ _ _ hJ]
  change Ideal.Quotient.factor hJ
      (s2e_adic_scalar_quotient_equiv I n
        (f.toLinearMap.reduceModIdeal (I ^ n) (x.val n))) =
    s2e_adic_quotient_ring_map J J f.toRingHom hf n
      (Ideal.Quotient.factor hJ (s2e_adic_scalar_quotient_equiv I n (x.val n)))
  generalize x.val n = z
  induction z using Submodule.Quotient.induction_on with
  | H s =>
    change Ideal.Quotient.factor hJ
      (s2e_adic_scalar_quotient_equiv I n (Submodule.Quotient.mk (f s))) = _
    rw [s2e_adic_scalar_quotient_equiv_mk, s2e_adic_scalar_quotient_equiv_mk]
    rfl

#print axioms s2e_adic_scalar_extension_map
/-- A base-algebra endomorphism preserves every extended base ideal.
Source: Mathlib, Ideal.map_map and AlgHom.commutes. -/
theorem s2e_algHom_map_extended_ideal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (f : S →ₐ[R] S) :
    (I.map (algebraMap R S)).map f.toRingHom = I.map (algebraMap R S) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext f.commutes

#print axioms s2e_algHom_map_extended_ideal
/-- Conjugation by scalar comparison gives the canonical adic algebra action.
Source: Mathlib, LinearEquiv.apply_symm_apply; the finite quotient comparison. -/
theorem s2e_adic_scalar_extension_conjugate
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (f : S →ₐ[R] S)
    (x : AdicCompletion (I.map (algebraMap R S)) S) :
    let e := s2e_adic_scalar_extension_equiv (S := S) I
    e (AdicCompletion.map I f.toLinearMap (e.symm x)) =
      s2e_adic_ring_map _ _ f.toRingHom (s2e_algHom_map_extended_ideal I f).le x := by
  dsimp only
  rw [s2e_adic_scalar_extension_map, LinearEquiv.apply_symm_apply]

#print axioms s2e_adic_scalar_extension_conjugate
/-- Scalar comparison identifies the base image with the canonical adic ring map.
Source: Mathlib, AdicCompletion.map_val_apply; finite quotient representatives. -/
theorem s2e_adic_scalar_extension_algebraMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (x : AdicCompletion I R) :
    s2e_adic_scalar_extension_equiv I
        (AdicCompletion.map I (Algebra.linearMap R S) x) =
      s2e_adic_ring_map I (I.map (algebraMap R S)) (algebraMap R S) le_rfl x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2e_adic_ring_map_eval]
  let J := I.map (algebraMap R S)
  have hJ : (J ^ n • ⊤ : Ideal S) ≤ J ^ n := by simp
  have hI : (I ^ n • ⊤ : Ideal R) ≤ I ^ n := by simp
  rw [← AdicCompletion.factor_eval_eq_evalₐ _ _ hJ,
    ← AdicCompletion.factor_eval_eq_evalₐ _ _ hI]
  change Ideal.Quotient.factor hJ
      (s2e_adic_scalar_quotient_equiv I n
        ((Algebra.linearMap R S).reduceModIdeal (I ^ n) (x.val n))) =
    s2e_adic_quotient_ring_map I J (algebraMap R S) le_rfl n
      (Ideal.Quotient.factor hI (x.val n))
  generalize x.val n = z
  induction z using Submodule.Quotient.induction_on with
  | H r =>
    change Ideal.Quotient.factor hJ
      (s2e_adic_scalar_quotient_equiv I n
        (Submodule.Quotient.mk (algebraMap R S r))) = _
    rw [s2e_adic_scalar_quotient_equiv_mk]
    rfl

#print axioms s2e_adic_scalar_extension_algebraMap
end HodgeLean.Foundations.Program

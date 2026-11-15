import HodgeLean.Foundations.Program.SchoenCycleAdicCoordinates
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Actual ring maps on adic limits -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An ideal-preserving ring map induces maps on every power quotient.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_adic_quotient_ring_map
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hf : I.map f ≤ J) (n : ℕ) : (R ⧸ I ^ n) →+* (S ⧸ J ^ n) :=
  Ideal.quotientMap (J ^ n) f (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact pow_le_pow_left' hf n)

#print axioms s2e_adic_quotient_ring_map

/-- An ideal-preserving ring map induces a ring map on adic limits.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Mathlib, AdicCompletion.liftRingHom. -/
def s2e_adic_ring_map
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hf : I.map f ≤ J) : AdicCompletion I R →+* AdicCompletion J S :=
  s2e_adic_coordinates_map I J (s2e_adic_quotient_ring_map I J f hf) (by
    intro m n h z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [s2e_adic_quotient_ring_map, Ideal.quotientMap_mk,
      Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk])

#print axioms s2e_adic_ring_map

/-- The induced adic ring map has the specified finite quotient evaluations.
Source: Mathlib, AdicCompletion.evalₐ_liftRingHom. -/
theorem s2e_adic_ring_map_eval
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hf : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (s2e_adic_ring_map I J f hf x) =
      s2e_adic_quotient_ring_map I J f hf n (AdicCompletion.evalₐ I n x) := by
  unfold s2e_adic_ring_map s2e_adic_coordinates_map
  generalize_proofs
  apply AdicCompletion.evalₐ_liftRingHom
  assumption

#print axioms s2e_adic_ring_map_eval

/-- The induced adic ring map extends the specified original ring map.
Source: Mathlib, AdicCompletion.evalₐ_of and Ideal.quotientMap_mk. -/
theorem s2e_adic_ring_map_of
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hf : I.map f ≤ J) (r : R) :
    s2e_adic_ring_map I J f hf (AdicCompletion.of I R r) =
      AdicCompletion.of J S (f r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2e_adic_ring_map_eval, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  rfl

#print axioms s2e_adic_ring_map_of

/-- Compatibility of finite coordinates with endomorphisms implies compatibility
of the corresponding adic coordinate equivalence.
Source: Mathlib, AdicCompletion.ext_evalₐ; equality is tested at every finite order. -/
theorem s2e_adic_coordinates_equiv_natural
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    (f : R →+* R) (hf : I.map f ≤ I) (g : S →+* S) (hg : J.map g ≤ J)
    (e : ∀ n : ℕ, (R ⧸ I ^ n) ≃+* (S ⧸ J ^ n))
    (E : AdicCompletion I R ≃+* AdicCompletion J S)
    (hE : ∀ n x, AdicCompletion.evalₐ J n (E x) = e n (AdicCompletion.evalₐ I n x))
    (he : ∀ n z, e n (s2e_adic_quotient_ring_map I I f hf n z) =
      s2e_adic_quotient_ring_map J J g hg n (e n z)) (x : AdicCompletion I R) :
    E (s2e_adic_ring_map I I f hf x) = s2e_adic_ring_map J J g hg (E x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [hE, s2e_adic_ring_map_eval, he, s2e_adic_ring_map_eval, hE]

#print axioms s2e_adic_coordinates_equiv_natural

/-- The induced maps on adic rings respect composition of the original ring maps.
Source: Mathlib, AdicCompletion.ext_evalₐ; the quotient maps respect composition. -/
theorem s2e_adic_ring_map_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (f : R →+* S) (hf : I.map f ≤ J) (g : S →+* T) (hg : J.map g ≤ K)
    (hgf : I.map (g.comp f) ≤ K) (x : AdicCompletion I R) :
    s2e_adic_ring_map J K g hg (s2e_adic_ring_map I J f hf x) =
      s2e_adic_ring_map I K (g.comp f) hgf x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2e_adic_ring_map_eval, s2e_adic_ring_map_eval, s2e_adic_ring_map_eval]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr]
  rfl

#print axioms s2e_adic_ring_map_comp
/-- Bijective finite quotient maps induce a bijective map on adic rings.
Source: Mathlib, AdicCompletion.ext_evalₐ and compatible quotient equivalences. -/
theorem s2e_adic_ring_map_bijective
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (s2e_adic_quotient_ring_map I J f hf n)) :
    Function.Bijective (s2e_adic_ring_map I J f hf) := by
  let e := fun n => RingEquiv.ofBijective (s2e_adic_quotient_ring_map I J f hf n) (hb n)
  have hc : ∀ {m n : ℕ} (h : m ≤ n) z,
      Ideal.Quotient.factorPow J h (e n z) =
        e m (Ideal.Quotient.factorPow I h z) := by
    intro m n h z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  obtain ⟨E, hE⟩ := s2e_adic_coordinates_equiv I J e hc
  have heq : (s2e_adic_ring_map I J f hf : AdicCompletion I R → AdicCompletion J S) = E := by
    funext x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [s2e_adic_ring_map_eval, hE]
    rfl
  rw [heq]
  exact E.bijective

#print axioms s2e_adic_ring_map_bijective
end HodgeLean.Foundations.Program

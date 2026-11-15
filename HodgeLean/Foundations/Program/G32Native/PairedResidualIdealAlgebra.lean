import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Residual union equations before conormal passage -/

namespace HodgeLean.Foundations.Program.G32Native

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A regular residual equation modulo the second component computes the union ideal. -/
theorem residual_principal_inf_kernel (f : R →+* S) (x : R)
    (hx : ∀ a : S, f x * a = 0 → a = 0) :
    Ideal.span {x} ⊓ RingHom.ker f = Ideal.span {x} * RingHom.ker f := by
  apply le_antisymm
  · intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha.1
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨b, ?_, hb.symm⟩
    apply RingHom.mem_ker.mpr
    apply hx
    rw [← map_mul, ← hb]
    exact RingHom.mem_ker.mp ha.2
  · exact Ideal.mul_le_inf

/-- Polynomial residual directions remain regular over arbitrary coefficient quotients. -/
theorem residual_polynomial_inf (I : Ideal R) :
    Ideal.span {Polynomial.X} ⊓ I.map (Polynomial.C : R →+* Polynomial R) =
      Ideal.span {Polynomial.X} * I.map (Polynomial.C : R →+* Polynomial R) := by
  have hker : RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk I)) =
      I.map (Polynomial.C : R →+* Polynomial R) := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  rw [← hker]
  apply residual_principal_inf_kernel
  intro a ha
  have he : Polynomial.X * a = 0 := by
    simpa only [Polynomial.coe_mapRingHom, Polynomial.map_X] using ha
  exact Polynomial.isRegular_X.left (he.trans (mul_zero _).symm)

/-- A two-axis node has the literal product equation for its union. -/
theorem residual_polynomial_node (a : R) :
    Ideal.span {(Polynomial.X : Polynomial R)} ⊓ Ideal.span {Polynomial.C a} =
      Ideal.span {Polynomial.X * Polynomial.C a} := by
  have hmap : (Ideal.span {a}).map (Polynomial.C : R →+* Polynomial R) =
      Ideal.span {Polynomial.C a} := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [← hmap, residual_polynomial_inf, hmap, Ideal.span_singleton_mul_span_singleton]

#print axioms residual_principal_inf_kernel
#print axioms residual_polynomial_inf
#print axioms residual_polynomial_node

end HodgeLean.Foundations.Program.G32Native

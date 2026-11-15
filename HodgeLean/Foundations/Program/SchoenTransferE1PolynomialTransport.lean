import HodgeLean.Foundations.Program.SchoenTransferE1PrimitiveFixed

/-! Polynomial transport for component maps of a rational representation. -/
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- An intertwining linear map transports every polynomial in the operators.
Source: polynomial evaluation and induction on monomials. -/
theorem s4_e1_polynomial_intertwines
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (p : V →ₗ[ℚ] W) (f : Module.End ℚ V) (g : Module.End ℚ W)
    (h : ∀ x, p (f x) = g (p x)) (q : Polynomial ℚ) (x : V) :
    p (Polynomial.aeval f q x) = Polynomial.aeval g q (p x) := by
  have hpow (n : ℕ) (y : V) : p ((f ^ n) y) = (g ^ n) (p y) := by
    induction n with
    | zero => simp only [pow_zero, Module.End.one_apply]
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, h, ih,
        pow_succ', Module.End.mul_apply]
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
      simp only [map_add, LinearMap.add_apply, hq, hr]
  | monomial n a =>
      simp only [Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.algebraMap_end_apply, map_smul, hpow]

/-- A component fixed by its residual operator vanishes when the original
vector belongs to the primitive kernel and the component map intertwines.
Source: Schoen (1988), Lemma 1.1, p. 5; polynomial transport and cyclotomic coprimality. -/
theorem s4_e1_fixed_primitive_component_eq_zero
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (p : V →ₗ[ℚ] W) (f : Module.End ℚ V) (g : Module.End ℚ W)
    (h : ∀ x, p (f x) = g (p x)) (m : ℕ) (hm : 3 ≤ m) (x : V)
    (hx : g (p x) = p x)
    (hp : Polynomial.aeval f (Polynomial.cyclotomic m ℚ) x = 0) : p x = 0 := by
  apply s4_e1_primitive_fixed_eq_zero g m hm (p x) hx
  rw [← s4_e1_polynomial_intertwines p f g h, hp, map_zero]

#print axioms s4_e1_polynomial_intertwines
#print axioms s4_e1_fixed_primitive_component_eq_zero
end HodgeLean.Foundations.Program

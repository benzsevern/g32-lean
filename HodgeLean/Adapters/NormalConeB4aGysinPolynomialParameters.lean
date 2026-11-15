import HodgeLean.Adapters.NormalConeB4aGysinRegularSourceOpen
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section
namespace HodgeLean.Adapters

/-- The coordinate list generates the ideal of evaluation at the zero parameter. -/
theorem a3b4a_gysin_zero_parameter_ideal
    {k : Type*} [CommRing k] (n : ℕ) :
    Ideal.ofList (List.ofFn (fun j : Fin n => (MvPolynomial.X j : MvPolynomial (Fin n) k))) =
      RingHom.ker (MvPolynomial.aeval (0 : Fin n → k)) := by
  classical
  let I := Ideal.ofList (List.ofFn
    (fun j : Fin n => (MvPolynomial.X j : MvPolynomial (Fin n) k)))
  have hX (j : Fin n) : (MvPolynomial.X j : MvPolynomial (Fin n) k) ∈ I :=
    Ideal.subset_span (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have hconst (f : MvPolynomial (Fin n) k) :
      f - MvPolynomial.C (MvPolynomial.constantCoeff f) ∈ I := by
    induction f using MvPolynomial.induction_on with
    | C a =>
      simpa only [MvPolynomial.constantCoeff_C, sub_self] using I.zero_mem
    | add f g hf hg =>
      simpa only [map_add, MvPolynomial.C_add, add_sub_add_comm] using I.add_mem hf hg
    | mul_X f j _ =>
      simpa only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero] using
        I.mul_mem_left f (hX j)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
    change MvPolynomial.aeval (0 : Fin n → k) (MvPolynomial.X j) = 0
    exact MvPolynomial.aeval_X _ _
  · intro f hf
    change MvPolynomial.aeval (0 : Fin n → k) f = 0 at hf
    rw [MvPolynomial.aeval_zero, Algebra.algebraMap_self_apply] at hf
    simpa only [hf, map_zero, sub_zero] using hconst f

end HodgeLean.Adapters

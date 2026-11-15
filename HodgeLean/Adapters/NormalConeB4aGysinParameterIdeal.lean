import HodgeLean.Adapters.NormalConeB4aGysinPolynomialParameters

noncomputable section
namespace HodgeLean.Adapters

/-- Coordinate differences generate the ideal of any polynomial parameter value. -/
theorem a3b4a_gysin_parameter_ideal
    {k : Type*} [CommRing k] {n : ℕ} (a : Fin n → k) :
    Ideal.ofList (List.ofFn (fun j : Fin n =>
      (MvPolynomial.X j - MvPolynomial.C (a j) : MvPolynomial (Fin n) k))) =
      RingHom.ker (MvPolynomial.aeval a) := by
  classical
  let I := Ideal.ofList (List.ofFn (fun j : Fin n =>
    (MvPolynomial.X j - MvPolynomial.C (a j) : MvPolynomial (Fin n) k)))
  have hX (j : Fin n) : MvPolynomial.X j - MvPolynomial.C (a j) ∈ I :=
    Ideal.subset_span (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have hdiff (f : MvPolynomial (Fin n) k) :
      f - MvPolynomial.C (MvPolynomial.aeval a f) ∈ I := by
    induction f using MvPolynomial.induction_on with
    | C b =>
      simpa only [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, sub_self] using I.zero_mem
    | add f g hf hg =>
      simpa only [map_add, MvPolynomial.C_add, add_sub_add_comm] using I.add_mem hf hg
    | mul_X f j hf =>
      have heq : f * MvPolynomial.X j - MvPolynomial.C (MvPolynomial.aeval a (f * MvPolynomial.X j)) =
          f * (MvPolynomial.X j - MvPolynomial.C (a j)) +
            (f - MvPolynomial.C (MvPolynomial.aeval a f)) * MvPolynomial.C (a j) := by
        rw [map_mul, MvPolynomial.aeval_X, map_mul]
        ring
      rw [heq]
      exact I.add_mem (I.mul_mem_left f (hX j)) (I.mul_mem_right (MvPolynomial.C (a j)) hf)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
    change MvPolynomial.aeval a (MvPolynomial.X j - MvPolynomial.C (a j)) = 0
    rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, sub_self]
  · intro f hf
    change MvPolynomial.aeval a f = 0 at hf
    simpa only [hf, map_zero, sub_zero] using hdiff f

end HodgeLean.Adapters

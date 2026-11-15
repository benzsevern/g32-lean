import HodgeLean.Foundations.Program.RigidStartingSystemExponentialClasses

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65r_unit_conjugate_pow {M : Type*} [Monoid M] (D : Mˣ) (X : M) (e : ℕ) :
    (D.val*X*(D⁻¹).val)^e = D.val*X^e*(D⁻¹).val := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ,ih,pow_succ]; simp [mul_assoc]

theorem b65r_residue_power_class (i : Fin 4) (e : ℕ) :
    ∃ D : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
      D.val*NormedSpace.exp ((2*Real.pi*Complex.I) •
        ((e : ℂ) • b65r_operator (b65r_residues i)))*(D⁻¹).val =
        b65r_operator (b4b_toMatrix ((b4b_generators i)^e)) := by
  letI : NormedAlgebra ℚ ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  obtain ⟨D,hD⟩ := b65r_residue_exponential_class i
  refine ⟨D,?_⟩
  rw [smul_comm, Nat.cast_smul_eq_nsmul, NormedSpace.exp_nsmul,
    ← b65r_unit_conjugate_pow, hD]
  change (b65r_operatorEquiv 4 (b4b_toMatrix (b4b_generators i)))^e =
    b65r_operatorEquiv 4 (b4b_toMatrix ((b4b_generators i)^e))
  rw [map_pow,map_pow]

theorem b65r_change_local_class {M : Type*} [Monoid M]
    (X Y Z : M) (C D : Mˣ) (hC : X = C.val*Y*(C⁻¹).val)
    (hD : D.val*Y*(D⁻¹).val = Z) :
    ∃ U : Mˣ, X = U.val*Z*(U⁻¹).val := by
  refine ⟨C*D⁻¹,?_⟩
  rw [← hD,hC]
  simp [mul_assoc]

end HodgeLean.Foundations.Program

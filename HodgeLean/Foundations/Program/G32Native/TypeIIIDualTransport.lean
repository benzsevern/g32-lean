import HodgeLean.Foundations.DualForm

noncomputable section
open Module
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program.G32Native
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- Contraction reverses the quadratic action for a Rosati-skew operator. -/
theorem typeIII_contract_anticommutes {ω : ⋀[ℚ]^2 V} (J : V →ₗ[ℚ] V)
    (hR : IsRosatiSkew ω J) (φ : Dual ℚ V) :
    J (contract ω φ) = -contract ω (J.dualMap φ) := by
  have h := LinearMap.congr_fun hR φ
  change contract ω (J.dualMap φ) = -(J (contract ω φ)) at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

/-- On contraction images the cohomology Hermitian expression is minus the
conjugate of the homology expression. The imaginary coefficient has the same
sign while the real coefficient changes sign. -/
theorem typeIII_dual_hermitian_expression {ω : ⋀[ℚ]^2 V}
    (hω : IsNondegenerate ω) (J : V →ₗ[ℚ] V) (hR : IsRosatiSkew ω J)
    (φ ψ : Dual ℚ V) :
    (⟨dualForm hω (contract ω φ) (J (contract ω ψ)),
        dualForm hω (contract ω φ) (contract ω ψ)⟩ : QuadraticAlgebra ℚ (-3) 0) =
      -star (⟨(J.dualMap ψ) (contract ω φ), ψ (contract ω φ)⟩ :
        QuadraticAlgebra ℚ (-3) 0) := by
  rw [typeIII_contract_anticommutes J hR ψ, map_neg,
    dualForm_contract_contract, dualForm_contract_contract]
  ext <;> simp

/-- Inverse contraction also reverses the quadratic generator. -/
theorem typeIII_inverse_contract_anticommutes {ω : ⋀[ℚ]^2 V}
    (hω : IsNondegenerate ω) (J : V →ₗ[ℚ] V) (hR : IsRosatiSkew ω J) (x : V) :
    (contractEquiv hω).symm (J x) = -J.dualMap ((contractEquiv hω).symm x) := by
  apply (contractEquiv hω).injective
  simp only [LinearEquiv.apply_symm_apply, map_neg, contractEquiv_apply]
  have h := typeIII_contract_anticommutes J hR ((contractEquiv hω).symm x)
  rw [contract_contractEquiv_symm] at h
  exact h

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_contract_anticommutes
#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_dual_hermitian_expression

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_inverse_contract_anticommutes

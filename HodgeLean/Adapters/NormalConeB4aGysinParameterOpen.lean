import HodgeLean.Adapters.NormalConeB4aGysinFiniteParameters
import Mathlib.RingTheory.Localization.BaseChange

/-! # Finite flat normalization on a principal parameter open -/

noncomputable section
namespace HodgeLean.Adapters

/-- Finite polynomial parameters have a principal open on which the full
base-changed algebra is finite and flat over the localized parameter ring. -/
theorem a3b4a_gysin_finite_flat_parameter_open
    {k R : Type} [Field k] [CommRing R] [Nontrivial R]
    [Algebra k R] [Algebra.FiniteType k R] :
    ∃ (d : ℕ) (φ : MvPolynomial (Fin d) k →ₐ[k] R),
      Function.Injective φ ∧ φ.Finite ∧
      letI : Algebra (MvPolynomial (Fin d) k) R := φ.toRingHom.toAlgebra
      ∃ a : MvPolynomial (Fin d) k, a ≠ 0 ∧
        Module.Finite (Localization.Away a)
          (TensorProduct (MvPolynomial (Fin d) k) (Localization.Away a) R) ∧
        Module.Flat (Localization.Away a)
          (TensorProduct (MvPolynomial (Fin d) k) (Localization.Away a) R) := by
  obtain ⟨d, φ, hinj, hfin, hflat⟩ :=
    a3b4a_gysin_finite_parameters_generic_flat (k := k) (R := R)
  refine ⟨d, φ, hinj, hfin, ?_⟩
  let P := MvPolynomial (Fin d) k
  letI : Algebra P R := φ.toRingHom.toAlgebra
  have : Module.Finite P R := hfin
  obtain ⟨a, ha, hflat⟩ := hflat
  let T := TensorProduct P (Localization.Away a) R
  letI : Algebra R T := Algebra.TensorProduct.rightAlgebra
  refine ⟨a, ha, inferInstance, ?_⟩
  exact HodgeLean.GenericFreeness.flat_localization_of_flat_localizedModule
    (A := P) (B := R) (A' := Localization.Away a) (B' := T) a hflat

end HodgeLean.Adapters

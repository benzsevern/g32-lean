import HodgeLean.Adapters.NormalConeB4aGysinSliceFlat
import HodgeLean.Foundations.Mathlib.GenericFreeness
import Mathlib.RingTheory.NoetherNormalization

/-! # Finite parameter maps with generic flatness

Noether normalization applies to the full affine algebra, including nilpotents.
Generic flatness supplies a principal open on the parameter space.
-/

noncomputable section
namespace HodgeLean.Adapters

/-- Every nonzero finite type algebra has finite polynomial parameters for which
a nonempty principal open of the parameter space gives a flat localized module. -/
theorem a3b4a_gysin_finite_parameters_generic_flat
    {k R : Type} [Field k] [CommRing R] [Nontrivial R]
    [Algebra k R] [Algebra.FiniteType k R] :
    ∃ (d : ℕ) (φ : MvPolynomial (Fin d) k →ₐ[k] R),
      Function.Injective φ ∧ φ.Finite ∧
      letI : Algebra (MvPolynomial (Fin d) k) R := φ.toRingHom.toAlgebra
      ∃ a : MvPolynomial (Fin d) k, a ≠ 0 ∧
        Module.Flat (MvPolynomial (Fin d) k) (LocalizedModule.Away a R) := by
  obtain ⟨d, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  refine ⟨d, φ, hinj, hfin, ?_⟩
  letI : Algebra (MvPolynomial (Fin d) k) R := φ.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin d) k) R := hfin
  obtain ⟨a, ha, hflat⟩ := HodgeLean.GenericFreeness.genFlat_of_finiteType
    (A := MvPolynomial (Fin d) k) (B := R)
  exact ⟨a, ha, hflat a (dvd_refl a)⟩

end HodgeLean.Adapters

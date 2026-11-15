import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Analysis.Complex.Basic

/-! # Algebraic differentials of etale coordinate sections -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Differentials of actual etale polynomial coordinates form a basis of the algebraic differential module.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_etale_coordinate_differential_basis
    {n : ℕ} (A : Type) [CommRing A] [Algebra ℂ A]
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (hφ : φ.toRingHom.Etale) :
    ∃ b : Module.Basis (Fin n) A Ω[A⁄ℂ],
      ∀ i, b i = KaehlerDifferential.D ℂ A (φ (MvPolynomial.X i)) := by
  letI : Algebra (MvPolynomial (Fin n) ℂ) A := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) A :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  letI : Algebra.Etale (MvPolynomial (Fin n) ℂ) A :=
    RingHom.etale_algebraMap.mp hφ
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
    ℂ (MvPolynomial (Fin n) ℂ) A
  refine ⟨((KaehlerDifferential.mvPolynomialBasis ℂ (Fin n)).baseChange A).map e, ?_⟩
  intro i
  simp only [e, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

/-- Algebraic tangent derivations on an etale coordinate ring are determined by the coordinate sections.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_etale_coordinate_derivation_ext
    {n : ℕ} (A : Type) [CommRing A] [Algebra ℂ A]
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (hφ : φ.toRingHom.Etale)
    (M : Type) [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M]
    (D₁ D₂ : Derivation ℂ A M)
    (h : ∀ i, D₁ (φ (MvPolynomial.X i)) = D₂ (φ (MvPolynomial.X i))) :
    D₁ = D₂ := by
  obtain ⟨b, hb⟩ := s2e_etale_coordinate_differential_basis A φ hφ
  have he : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential := by
    apply b.ext
    intro i
    rw [hb, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h i
  ext a
  have ha := congrArg (fun F : Ω[A⁄ℂ] →ₗ[A] M => F (KaehlerDifferential.D ℂ A a)) he
  simpa only [Derivation.liftKaehlerDifferential_comp_D] using ha

end HodgeLean.Foundations.Program

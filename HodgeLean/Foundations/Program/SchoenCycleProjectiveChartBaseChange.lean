import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartQuotient
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Coefficient change for actual projective chart rings -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The actual integral projective chart ring is the normalized quotient over the integers.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
def s2e_integralChartRingEquivInt {n : ℕ} (i : Fin (n + 1)) :
    HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) ≃+*
      MvPolynomial (Fin (n + 1)) ℤ ⧸
        Ideal.span ({MvPolynomial.X i - 1} : Set (MvPolynomial (Fin (n + 1)) ℤ)) := by
  let e : UniversalRing n ≃+* MvPolynomial (Fin (n + 1)) ℤ :=
    MvPolynomial.mapEquiv (Fin (n + 1)) (ULift.ringEquiv (R := ℤ))
  refine (s2e_integralChartRingEquiv i).trans (Ideal.quotientEquiv _ _ e ?_)
  have hX : e (MvPolynomial.X i) = MvPolynomial.X i := by
    change MvPolynomial.map (ULift.ringEquiv (R := ℤ)).toRingHom (MvPolynomial.X i) = _
    exact MvPolynomial.map_X _ _
  rw [Ideal.map_span]
  simp only [Set.image_singleton]
  change Ideal.span ({MvPolynomial.X i - 1} : Set (MvPolynomial (Fin (n + 1)) ℤ)) =
    Ideal.span {e (MvPolynomial.X i - 1)}
  rw [map_sub, map_one, hX]

/-- Base change of the actual integral standard chart is the normalized polynomial quotient over the new coefficient ring.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
def s2e_baseChangedChartAlgEquiv (R : Type*) [CommRing R] {n : ℕ} (i : Fin (n + 1)) :
    R ⊗[ℤ] HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) ≃ₐ[R]
      MvPolynomial (Fin (n + 1)) R ⧸
        Ideal.span ({MvPolynomial.X i - 1} : Set (MvPolynomial (Fin (n + 1)) R)) := by
  let P := MvPolynomial (Fin (n + 1)) ℤ
  let I := Ideal.span ({MvPolynomial.X i - 1} : Set P)
  let e₁ : R ⊗[ℤ] HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) ≃ₐ[R]
      R ⊗[ℤ] (P ⧸ I) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) (s2e_integralChartRingEquivInt i).toIntAlgEquiv
  let e₂ := Algebra.TensorProduct.tensorQuotientEquiv (R := ℤ) R P R I
  let eP : R ⊗[ℤ] P ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
    MvPolynomial.algebraTensorAlgEquiv ℤ R
  refine e₁.trans (e₂.trans (Ideal.quotientEquivAlg _ _ eP ?_))
  have hrel : eP ((1 : R) ⊗ₜ[ℤ] (MvPolynomial.X i - 1 : P)) = MvPolynomial.X i - 1 := by
    change MvPolynomial.algebraTensorAlgEquiv ℤ R
      ((1 : R) ⊗ₜ[ℤ] (MvPolynomial.X i - 1 : P)) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
    simp only [map_sub, MvPolynomial.map_X, map_one, one_smul]
  change Ideal.span ({MvPolynomial.X i - 1} : Set (MvPolynomial (Fin (n + 1)) R)) =
    Ideal.map eP.toRingHom
      (Ideal.map (Algebra.TensorProduct.includeRight (R := ℤ) (A := R) (B := P)).toRingHom I)
  rw [Ideal.map_map, Ideal.map_span]
  simp only [Set.image_singleton]
  change Ideal.span ({MvPolynomial.X i - 1} : Set (MvPolynomial (Fin (n + 1)) R)) =
    Ideal.span {eP ((1 : R) ⊗ₜ[ℤ] (MvPolynomial.X i - 1 : P))}
  rw [hrel]

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs
import Mathlib.RingTheory.RingHom.Etale

/-! # Centering algebraic point coordinates

Translation of polynomial coordinates is an algebra isomorphism, so it
preserves the étale coordinate map while centering a marked evaluation.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace AlgebraicGeometry.SingularCycles

def polynomialCoordinateShift {d : ℕ} (a : Fin d → ℂ) :
    MvPolynomial (Fin d) ℂ ≃ₐ[ℂ] MvPolynomial (Fin d) ℂ :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval (fun j => MvPolynomial.X j - MvPolynomial.C (a j)))
    (MvPolynomial.aeval (fun j => MvPolynomial.X j + MvPolynomial.C (a j)))
    (by apply MvPolynomial.algHom_ext; intro j; simp)
    (by apply MvPolynomial.algHom_ext; intro j; simp)

theorem polynomialCoordinateShift_X {d : ℕ} (a : Fin d → ℂ) (j : Fin d) :
    polynomialCoordinateShift a (MvPolynomial.X j) = MvPolynomial.X j - MvPolynomial.C (a j) := by
  exact MvPolynomial.aeval_X _ _

def centeredCoordinateHom {d : ℕ} {B : Type} [CommRing B] [Algebra ℂ B]
    (φ : MvPolynomial (Fin d) ℂ →ₐ[ℂ] B) (u : B →ₐ[ℂ] ℂ) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] B :=
  φ.comp (polynomialCoordinateShift (fun j => u (φ (MvPolynomial.X j)))).toAlgHom

theorem centeredCoordinateHom_evaluation {d : ℕ} {B : Type} [CommRing B] [Algebra ℂ B]
    (φ : MvPolynomial (Fin d) ℂ →ₐ[ℂ] B) (u : B →ₐ[ℂ] ℂ) :
    u.comp (centeredCoordinateHom φ u) = MvPolynomial.aeval (0 : Fin d → ℂ) := by
  apply MvPolynomial.algHom_ext
  intro j
  change u (φ (polynomialCoordinateShift (fun k => u (φ (MvPolynomial.X k)))
    (MvPolynomial.X j))) = MvPolynomial.aeval (0 : Fin d → ℂ) (MvPolynomial.X j)
  rw [polynomialCoordinateShift_X, map_sub, map_sub, MvPolynomial.algHom_C, u.commutes,
    MvPolynomial.aeval_X]
  exact sub_self _

theorem centeredCoordinateHom_etale {d : ℕ} {B : Type} [CommRing B] [Algebra ℂ B]
    (φ : MvPolynomial (Fin d) ℂ →ₐ[ℂ] B) (u : B →ₐ[ℂ] ℂ) (hφ : φ.toRingHom.Etale) :
    (centeredCoordinateHom φ u).toRingHom.Etale := by
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective
      (polynomialCoordinateShift (fun j => u (φ (MvPolynomial.X j)))).bijective) hφ

end AlgebraicGeometry.SingularCycles

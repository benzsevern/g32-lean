import HodgeLean.Foundations.ChowTheoremProofs
import HodgeLean.Foundations.AnalyticDivisorAlgebraic2

/-! # Analytic cones: frozen first segment

An implication from closed analyticity on the whole affine space and scalar
stability to finite homogeneous polynomial equations. Analytic extension across
the vertex and the projective-to-scheme comparison remain deferred.
No general set-level Chow assertion is made here.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations
open Set

/-- A point outside a closed analytic cone is separated by a homogeneous polynomial.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
proof of Chow's theorem by homogeneous Taylor terms. -/
theorem chow_cone_separation (n : ℕ) (Z : Set (Fin n → ℂ))
    (hZ : IsClosedAnalytic (Fin n → ℂ) Z)
    (hscale : ∀ (t : ℂ) (z : Fin n → ℂ), z ∈ Z → t • z ∈ Z)
    (x : Fin n → ℂ) (hx : x ∉ Z) :
    ∃ (d : ℕ) (P : MvPolynomial (Fin n) ℂ), P.IsHomogeneous d ∧
      (∀ z ∈ Z, MvPolynomial.eval z P = 0) ∧ MvPolynomial.eval x P ≠ 0 :=
  chow_cone_separation_aux n Z hZ hscale x hx

/-- A closed analytic cone has finitely many homogeneous polynomial equations.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
proof of Chow's theorem; Hilbert's basis theorem applied to the separating polynomials. -/
theorem chow_cone_algebraic (n : ℕ) (Z : Set (Fin n → ℂ))
    (hZ : IsClosedAnalytic (Fin n → ℂ) Z)
    (hscale : ∀ (t : ℂ) (z : Fin n → ℂ), z ∈ Z → t • z ∈ Z) :
    ∃ (m : ℕ) (d : Fin m → ℕ) (P : Fin m → MvPolynomial (Fin n) ℂ),
      (∀ i, (P i).IsHomogeneous (d i)) ∧
      Z = {z | ∀ i, MvPolynomial.eval z (P i) = 0} :=
  chow_cone_algebraic_aux n Z hZ hscale

/-- The cone over the coordinate hyperplane in the projective plane separates (1,1,1).
Source: Griffiths--Harris, Chapter 1 §3, homogeneous coordinates. -/
example : ∃ (d : ℕ) (P : MvPolynomial (Fin 3) ℂ), P.IsHomogeneous d ∧
    (∀ z : Fin 3 → ℂ, z 0 = 0 → MvPolynomial.eval z P = 0) ∧
    MvPolynomial.eval (fun _ ↦ 1) P ≠ 0 := by
  apply chow_cone_separation 3 {z | z 0 = 0}
  · exact AnalyticDivisorAlgebraic2.spec_isClosedAnalytic_zeroSet_of_differentiable
      (by fun_prop)
  · intro t z hz
    change t * z 0 = 0
    rw [hz, mul_zero]
  · exact one_ne_zero

/-- The coordinate hyperplane cone instantiates the finite-equations endpoint.
Source: Griffiths--Harris, Chapter 1 §3, homogeneous coordinates. -/
example : ∃ (m : ℕ) (d : Fin m → ℕ) (P : Fin m → MvPolynomial (Fin 3) ℂ),
    (∀ i, (P i).IsHomogeneous (d i)) ∧
    {z : Fin 3 → ℂ | z 0 = 0} = {z | ∀ i, MvPolynomial.eval z (P i) = 0} := by
  apply chow_cone_algebraic 3 {z | z 0 = 0}
  · exact AnalyticDivisorAlgebraic2.spec_isClosedAnalytic_zeroSet_of_differentiable
      (by fun_prop)
  · intro t z hz
    change t * z 0 = 0
    rw [hz, mul_zero]

end HodgeLean.Foundations

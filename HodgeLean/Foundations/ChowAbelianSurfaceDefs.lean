import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective

/-! # Scheme carriers for homogeneous equations

The carrier is the Zariski closure of the specified complex zero points.
No assertion that closure preserves the complex zero set is built into it.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Set
namespace HodgeLean.Foundations

/-- The Zariski closure of the projective complex zero points of a polynomial family.
The definition makes sense even for nonhomogeneous equations.
Source: Hartshorne, Algebraic Geometry, Chapter I §2, projective zero loci. -/
def chowEE_projectiveCarrier (n m : ℕ)
    (P : Fin m → MvPolynomial (Fin (n + 1)) ℂ) :
    Set (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)) :=
  closure {x | ∃ (z : Fin (n + 1) → ℂ) (hz : z ≠ 0),
    (∀ j, MvPolynomial.eval z (P j) = 0) ∧
      (ComplexProjectiveSpace.vectorToComplexPoint z hz).underlying = x}

/-- A nonzero constant equation has no projective zero points.
Source: Hartshorne, Algebraic Geometry, Chapter I §2. -/
example : chowEE_projectiveCarrier 1 1 (fun _ ↦ 1) = ∅ := by
  simp [chowEE_projectiveCarrier]

end HodgeLean.Foundations

module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Projective residue intersections
Implication from distinct residue coordinates in an adapted coefficient basis to
scheme ideals on projective charts and their global intersections.
Cartier generators and blowup transport are later units.
HC no distance; AV milestone no distance.
-/
@[expose] public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The reduced residue-coordinate hyperplane in the adapted coefficient basis.
Source: Schoen (1988), Lemma 2.3(iv,vi), printed pp. 13–14. -/
def s2e_s2b_residueIdeal (k : ℕ) (j : Fin (k + 1)) :
    (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨(projectiveSpaceBasicOpen k (MvPolynomial.X j)).carrierᶜ,
      (projectiveSpaceBasicOpen k (MvPolynomial.X j)).isOpen.isClosed_compl⟩

example (k : ℕ) (j : Fin (k + 1)) :
    (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData := s2e_s2b_residueIdeal k j

/-- The scheme intersection uses the sum of the actual residue ideals.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
def s2e_s2b_intersectionIdeal (k : ℕ) (T : Finset (Fin (k + 1))) :
    (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData :=
  ⨆ j ∈ T, s2e_s2b_residueIdeal k j

example (k : ℕ) : s2e_s2b_intersectionIdeal k ∅ = ⊥ := by
  simp [s2e_s2b_intersectionIdeal]

/-- Set the chart denominator to one and retain exactly the other coordinates.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; standard projective charts. -/
def s2e_s2b_chartHom {k : ℕ} (i : Fin (k + 1)) :
    HomogeneousLocalization.Away (UniversalGrading k) (MvPolynomial.X i) →+*
      MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ :=
  (MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)
    (fun j => if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩)).comp
      (chartAwayPolynomialHom i)

example {k : ℕ} (i : Fin (k + 1)) : s2e_s2b_chartHom i 1 = 1 := map_one _

/-- The standard affine chart morphism, with no redundant coordinate.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; standard projective charts. -/
def s2e_s2b_chart {k : ℕ} (i : Fin (k + 1)) :
    Spec ↧(MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ) ⟶
      ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) :=
  Limits.pullback.lift
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* _)))
    (Spec.map (CommRingCat.ofHom (s2e_s2b_chartHom i)) ≫
      Proj.awayι (UniversalGrading k) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ _) zero_lt_one)
    (Subsingleton.elim _ _)

example {k : ℕ} (i : Fin (k + 1)) :
    s2e_s2b_chart i ≫ ProjectiveSpace.toBase _ _ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* _)) :=
  Limits.pullback.lift_fst _ _ _

end HodgeLean.Foundations.Program

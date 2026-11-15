import HodgeLean.Foundations.Curves.SymmetricCharts.Defs
import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Symmetric curve branch constructions

The branch ideals use the retained insertion projection. Coordinate hyperplanes
are ideal sheaves on actual polynomial spectra.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option maxHeartbeats 400000

/-- Polynomial affine space with its specified complex structure map.
Source: Hartshorne, Algebraic Geometry, II.2.
HC no distance; AV milestone no distance.
-/
def affine (n : ℕ) : Over (Spec ↧ℂ) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ))))

example : (affine 2).left = Spec ↧(MvPolynomial (Fin 2) ℂ) := rfl

/-- The coordinate hyperplane, retaining its scheme ideal rather than its support.
Source: Hartshorne, Algebraic Geometry, II.5.
HC no distance; AV milestone no distance.
-/
def coordinateIdeal (n : ℕ) (i : Fin n) : (affine n).left.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span
    { (Scheme.ΓSpecIso ↧(MvPolynomial (Fin n) ℂ)).inv (MvPolynomial.X i) })

example (i : Fin 2) : coordinateIdeal 2 i =
    Scheme.IdealSheafData.ofIdealTop (Ideal.span
      { (Scheme.ΓSpecIso ↧(MvPolynomial (Fin 2) ℂ)).inv (MvPolynomial.X i) }) := rfl

/-- Evaluate an actual affine-space point on its specified coordinate section.
Source: Hartshorne, Algebraic Geometry, II.2, functor of points of affine space.
HC no distance; AV milestone no distance.
-/
def coordinateValue (n : ℕ) (p : ComplexPoint (affine n)) (i : Fin n) : ℂ :=
  (Scheme.ΓSpecIso ↧ℂ).hom
    (p.left.appTop ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin n) ℂ)).inv (MvPolynomial.X i)))

example (p : ComplexPoint (affine 2)) : coordinateValue 2 p 0 =
    (Scheme.ΓSpecIso ↧ℂ).hom
      (p.left.appTop ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin 2) ℂ)).inv (MvPolynomial.X (0 : Fin 2)))) := rfl

variable (C : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]

/-- The retained point-addition image ideal on the actual quotient.
Source: Milne, Jacobian Varieties, §3; Schoen (1988), §2, p. 12.
HC no distance; AV milestone no distance.
-/
def branchIdeal (h : ℕ) (b : ComplexPoint C) : (symmetricPower C (h+1)).left.IdealSheafData :=
  s2c_branchIdeal C (symmetricPower C (h+1)) h (projection C (h+1)) b

example (b : ComplexPoint C) : branchIdeal C 1 b =
    (s2c_branchInsertion C 1 b ≫ projection C 2).left.ker := rfl

/-- Scheme intersection: the sum of the branch ideals, including the empty sum.
Source: Hartshorne, Algebraic Geometry, II.5, scheme intersections.
HC no distance; AV milestone no distance.
-/
def intersectionIdeal (h k : ℕ) (b : Fin k → ComplexPoint C) :
    (symmetricPower C (h+1)).left.IdealSheafData := ⨆ i, branchIdeal C h (b i)

example (b : Fin 0 → ComplexPoint C) : intersectionIdeal C 1 0 b = ⊥ := by
  simp only [intersectionIdeal, iSup_of_empty]

/-- Insert the specified list of curve points before the residual ordered tuple.
Source: Milne, Jacobian Varieties, §3, addition of effective divisors.
HC no distance; AV milestone no distance.
-/
def multipleInsertion (h k : ℕ) (hk : k ≤ h+1) (b : Fin k → ComplexPoint C) :
    g3_power C (h+1-k) ⟶ g3_power C (h+1) :=
  s2_lift (k+(h+1-k))
    (Fin.addCases (fun i => CartesianMonoidalCategory.toUnit _ ≫ b i)
      (fun i => g3_proj C (h+1-k) i)) ≫
    eqToHom (congrArg (g3_power C) (Nat.add_sub_of_le hk))

example (b : Fin 2 → ComplexPoint C) :
    g3_power C 1 ⟶ g3_power C 3 := multipleInsertion C 2 2 (by omega) b

/-- The actual intersection subscheme over the complex base.
Source: Hartshorne, Algebraic Geometry, II.5.
HC no distance; AV milestone no distance.
-/
def branchIntersection (h k : ℕ) (b : Fin k → ComplexPoint C) : Over (Spec ↧ℂ) :=
  s2c_subscheme (symmetricPower C (h+1)) (intersectionIdeal C h k b)

example (b : Fin 2 → ComplexPoint C) :
    (branchIntersection C 1 2 b).left = (intersectionIdeal C 1 2 b).subscheme := rfl

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo

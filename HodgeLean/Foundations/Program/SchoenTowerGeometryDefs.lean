import HodgeLean.Foundations.Program.SchoenTowerDefs
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Branch ideals and transforms for the retained symmetric base
These constructions use scheme maps and ideal sheaves.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Insert the retained branch point in the first coordinate.
Source: Schoen (1988), §2, p. 12, the map defining Sⱼ. -/
def s2c_branchInsertion (Z : Over (Spec ↧ℂ)) (h : ℕ)
    (b : AlgebraicGeometry.ComplexPoint Z) : g3_power Z h ⟶ g3_power Z (h + 1) :=
  s2_lift (h + 1) (Fin.cases (CartesianMonoidalCategory.toUnit _ ≫ b)
    (fun i => g3_proj Z h i))

example (Z : Over (Spec ↧ℂ)) (h : ℕ) (b : AlgebraicGeometry.ComplexPoint Z) :
    s2c_branchInsertion Z h b = s2_lift (h + 1)
      (Fin.cases (CartesianMonoidalCategory.toUnit _ ≫ b) (fun i => g3_proj Z h i)) := rfl

/-- The ideal of the scheme image of b + SʰZ in the specified symmetric quotient.
Source: Schoen (1988), §2, p. 12, Sⱼ = γ(bⱼ × Zʰ). -/
def s2c_branchIdeal (Z B : Over (Spec ↧ℂ)) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) (b : AlgebraicGeometry.ComplexPoint Z) :
    B.left.IdealSheafData := (s2c_branchInsertion Z h b ≫ γ).left.ker

example (Z B : Over (Spec ↧ℂ)) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) (b : AlgebraicGeometry.ComplexPoint Z) :
    s2c_branchIdeal Z B h γ b = (s2c_branchInsertion Z h b ≫ γ).left.ker := rfl

/-- Reduced strict transform away from the specified centre.
For the smooth branch divisors this is their usual strict transform.
Source: Hartshorne, Algebraic Geometry, II.7; Schoen (1988), p. 14. -/
def s2c_strictTransform {X Y : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))), isClosed_closure⟩

example {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData) :
    s2c_strictTransform f D K = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))), isClosed_closure⟩ := rfl

/-- The subscheme of a complex scheme defined by an ideal sheaf.
Source: Hartshorne, Algebraic Geometry, II.5; Schoen (1988), p. 14, Kᵢ. -/
def s2c_subscheme (B : Over (Spec ↧ℂ)) (I : B.left.IdealSheafData) :
    Over (Spec ↧ℂ) := Over.mk (I.subschemeι ≫ B.hom)

example (B : Over (Spec ↧ℂ)) (I : B.left.IdealSheafData) :
    (s2c_subscheme B I).left = I.subscheme := rfl

/-- Inclusion of the specified subscheme over the complex base.
Source: Hartshorne, Algebraic Geometry, II.5. -/
def s2c_subschemeι (B : Over (Spec ↧ℂ)) (I : B.left.IdealSheafData) :
    s2c_subscheme B I ⟶ B := Over.homMk I.subschemeι

example (B : Over (Spec ↧ℂ)) (I : B.left.IdealSheafData) :
    (s2c_subschemeι B I).left = I.subschemeι := rfl

end HodgeLean.Foundations.Program

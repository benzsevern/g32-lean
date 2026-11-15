import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialOpens
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle

/-! # Literal coordinate ratios under the integral polynomial comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Integral normalized chart coordinates pull back to the literal native
coordinate ratio, preserving both numerator and denominator indices. -/
theorem conormal_integral_coordinate_ratio (k : ℕ) (i j : Fin (k + 1)) :
    (Proj.map (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)))
      (s2_polynomialIntegralCoordinates_irrelevant ℂ (Fin (k + 1)))).appLE
        (Proj.basicOpen (UniversalGrading k) (X i)) (ProjSpace.standardOpen ℂ k i)
        (by rw [Proj.map_preimage_basicOpen, s2_polynomialIntegralCoordinates_X])
        (Proj.awayToSection (UniversalGrading k) (X i) (chartCoordinate i j)) =
      ProjSpace.coordinateRatioSection ℂ k i j := by
  have h := ConcreteCategory.congr_hom
    (Proj.awayToSection_comp_appLE
      (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)))
      (s2_polynomialIntegralCoordinates_irrelevant ℂ (Fin (k + 1)))
      (isHomogeneous_X (ULift ℤ) i)) (chartCoordinate i j)
  let f := s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))
  have hgen (s : MvPolynomial (Fin (k + 1)) ℂ) (hs : f (X i) = s) :
      (Proj.map f (s2_polynomialIntegralCoordinates_irrelevant ℂ (Fin (k + 1)))).appLE
        (Proj.basicOpen (UniversalGrading k) (X i))
        (Proj.basicOpen (homogeneousSubmodule (Fin (k + 1)) ℂ) s)
        (by rw [← hs]; rfl)
        (Proj.awayToSection (UniversalGrading k) (X i) (chartCoordinate i j)) =
      Proj.awayToSection (homogeneousSubmodule (Fin (k + 1)) ℂ) s
        (Away.mk _ (hs ▸ f.map_mem (isHomogeneous_X (ULift ℤ) i)) 1 (f (X j))
          (by simpa using f.map_mem (isHomogeneous_X (ULift ℤ) j))) := by
    subst s
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom, chartCoordinate, Away.map_mk] using h
  simpa only [s2_polynomialIntegralCoordinates_X, f, ProjSpace.coordinateRatioSection,
    ProjSpace.ratio] using hgen (X i) (s2_polynomialIntegralCoordinates_X ℂ (Fin (k + 1)) i)

end HodgeLean.Foundations.Program.G32Native

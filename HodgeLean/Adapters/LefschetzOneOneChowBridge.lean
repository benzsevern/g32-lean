import HodgeLean.Adapters.LefschetzOneOneChowBridgeProofs
import HodgeLean.Adapters.LefschetzOneOneChowBridgeDefs

/-! # Set-level Chow to the bh4 consumer

An implication from set-level Chow, using all stage-24 algebraization fields.
The final composition retains bh4’s five open geometric obligations, listed in
docs/specs/LefschetzOneOneChowBridge.md. No general Chow theorem is constructed here.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic24
open Set
namespace HodgeLean.Adapters

/-- Transfer every component, multiplicity, support, and local equation from stage 24.
Source: gaga24_algebraization; Serre, GAGA, Théorème 3. -/
theorem bhg_algebraization_of_chow (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (D : bh4_LocalDivisorData X) :
    Nonempty (bh4_Algebraization X D) :=
  bhg_algebraization_of_chow_aux X hChow D

example : Nonempty (bh4_Algebraization Curves.E bhg_curveDivisor) :=
  bhg_algebraization_of_chow Curves.E gaga24_curve_chow bhg_curveDivisor

example : Nonempty (bh4_Algebraization Curves.E (bhg_emptyDivisor Curves.E)) :=
  bhg_algebraization_of_chow Curves.E gaga24_curve_chow (bhg_emptyDivisor Curves.E)

/-- Assemble the existing bh4 interface from set-level Chow.
Source: bhg_algebraization_of_chow; Serre, GAGA, Théorème 3. -/
theorem bhg_localDivisorDataAlgebraizes_of_chow (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    bh4_LocalDivisorDataAlgebraizes X :=
  bhg_localDivisorDataAlgebraizes_of_chow_aux X hChow

example : bh4_LocalDivisorDataAlgebraizes Curves.E :=
  bhg_localDivisorDataAlgebraizes_of_chow Curves.E gaga24_curve_chow

/-- Implication from set-level Chow via the existing bh4 composition.
Source: spec_bh4_lefschetzOneOneFor_of_localDivisorDataAlgebraizes;
finiteBetti_abelian; spec_bettiDeRhamIso_abelian. -/
theorem bhg_lefschetzOneOne_of_chow (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    LefschetzOneOneFor X :=
  bhg_lefschetzOneOne_of_chow_aux X hChow

example : LefschetzOneOneFor Curves.E :=
  bhg_lefschetzOneOne_of_chow Curves.E gaga24_curve_chow

end HodgeLean.Adapters

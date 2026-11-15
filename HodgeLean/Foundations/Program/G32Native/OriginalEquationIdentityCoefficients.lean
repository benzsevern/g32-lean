import HodgeLean.Foundations.Program.G32Native.OriginalRegularConormalSpanning
import HodgeLean.Foundations.Program.G32Native.OriginalAffineEquationFrameCoefficients
import HodgeLean.Foundations.Program.G32Native.RegularEquationCoefficientOperator

/-! # Choosing original equations with identity frame coefficients at a point -/
noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- An algebraic conormal frame has original regular ideal equations
whose regular coefficient matrix is the identity at the specified point.
Source: `originalRegularConormalValue_surjective`,
`originalAffineEquation_frame_coefficients`, and
`regularEquationCoefficientOperator_eq_id`. -/
theorem exists_original_equation_identity_coefficients
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (k m : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (U : Y.left.Opens) (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (x : ComplexPoint Y) (hx : x ∈ Point.overOpen U) :
    ∃ (u : Fin k → RingHom.ker (j.left.app A).hom)
      (r : Fin k → Fin k → Γ(Y.left, U)),
      (∀ (y : ComplexPoint Y) (hy : y ∈ Point.overOpen U) (i a : Fin k),
        i1_conormalFrameCoordinates j.left k U E y hy
          (originalRegularConormalValue j.left A hA (u i) y (hU hy)) a =
          Point.evaluate U (r i a) y) ∧
      regularEquationCoefficientOperator Y k U r x = ContinuousLinearMap.id ℂ (Fin k → ℂ) := by
  classical
  let b := i1_conormalFrameBasis j.left k U E x hx
  choose u hu using fun i : Fin k =>
    originalRegularConormalValue_surjective X Y j A hA x (hU hx) (b i)
  choose r hr _ using fun i : Fin k =>
    originalAffineEquation_frame_coefficients Y j.left A hA (u i) k m U hU E
  have hcoeff : ∀ (y : ComplexPoint Y) (hy : y ∈ Point.overOpen U) (i a : Fin k),
      i1_conormalFrameCoordinates j.left k U E y hy
        (originalRegularConormalValue j.left A hA (u i) y (hU hy)) a =
          Point.evaluate U (r i a) y := by
    intro y hy i a
    rw [originalRegularConormalValue_eq]
    exact hr i y hy a
  refine ⟨u, r, hcoeff, regularEquationCoefficientOperator_eq_id Y k U r x ?_⟩
  intro i a
  have hri := (hcoeff x hx i a).symm
  have heq := congrArg (fun w : i1_conormalFibre j.left x =>
    i1_conormalFrameCoordinates j.left k U E x hx w a) (hu i)
  have hcoord := Module.Basis.ofEquivFun_repr_apply
    (i1_conormalFrameCoordinates j.left k U E x hx) (b i) a
  exact hri.trans (heq.trans (hcoord.symm.trans
    (by simpa only [b, i1_conormalFrameBasis, eq_comm] using b.repr_self_apply i a)))

#print axioms exists_original_equation_identity_coefficients
end HodgeLean.Foundations.TubularEuler

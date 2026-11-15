import HodgeLean.Foundations.BundleThom.NormalFrameChartsHelpers
import HodgeLean.Foundations.BundleThom.ConormalFrameCoefficientHelpers
import HodgeLean.Foundations.BundleThom.DualCoordinateEvaluationHelpers

/-! # Evaluation along the inverse actual normal-frame coordinates

Sections on the frame's open domain give continuous inverse-coordinate evaluations.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle
namespace HodgeLean.Foundations.BundleThom

/-- Inverse normal-frame evaluation against any section on the frame domain is continuous.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, analytification of dual local frames. -/
theorem i1_normalFrameInverse_evaluation_continuous {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j)) :
    Continuous (fun p : ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ) =>
      ((i1_normalFrameEquiv j k U E).symm p).1.2
        (i1_conormalSectionValue j U s p.1.1 p.1.2)) := by
  let c : ↥(Point.overOpen U : Set (ComplexPoint Q)) → Fin k → ℂ :=
    fun x => i1_conormalFrameCoordinates j k U E x.1 x.2
      (i1_conormalSectionValue j U s x.1 x.2)
  have hc : Continuous c := i1_conormalFrameCoordinates_section_continuous j k U E s
  have heq : (fun p : ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ) =>
      ((i1_normalFrameEquiv j k U E).symm p).1.2
        (i1_conormalSectionValue j U s p.1.1 p.1.2)) =
      (fun p : ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ) =>
        ∑ i, p.2 i * c p.1 i) := by
    funext p
    have hd := i1_dualCoordinateEvaluation k
      (i1_conormalFrameBasis j k U E p.1.1 p.1.2) p.2
      (i1_conormalSectionValue j U s p.1.1 p.1.2)
    apply hd.trans
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z => p.2 i * z)
      (Module.Basis.ofEquivFun_repr_apply (i1_conormalFrameCoordinates j k U E p.1.1 p.1.2)
        (i1_conormalSectionValue j U s p.1.1 p.1.2) i)
  rw [heq]
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp continuous_snd).mul
      ((continuous_apply i).comp (hc.comp continuous_fst)))

end HodgeLean.Foundations.BundleThom

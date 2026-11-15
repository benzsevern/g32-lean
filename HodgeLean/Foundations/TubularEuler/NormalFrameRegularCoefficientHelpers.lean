import HodgeLean.Foundations.Analytic.Analytification
import HodgeLean.Foundations.BundleThom.ConormalFrameCoefficientHelpers
import HodgeLean.Foundations.BundleResolution.ModuleOpenRegularEvaluationHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold

/-! # Regular coefficients on the original normal-base open

Local section coefficients are evaluated on the original base scheme.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
open scoped ContDiff Manifold
namespace HodgeLean.Foundations.TubularEuler
open BundleThom BundleResolution

variable {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (k : ℕ)
variable (U : Q.left.Opens)
variable (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
  SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
variable (s : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶
  (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j))

def normalFrameSectionCoefficient (i : Fin k) : Γ(Q.left, U) :=
  U.topIso.hom (((s ≫ E.hom) ≫ i1_freeSheafProjection U.toScheme k i).val.app (.op ⊤)
    (1 : Γ(U.toScheme, ⊤)))

theorem normalFrameSectionCoefficient_evaluate
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) (i : Fin k) :
    i1_conormalFrameCoordinates j k U E x hx (i1_conormalSectionValue j U s x hx) i =
      Point.evaluate U (normalFrameSectionCoefficient j k U E s i) x := by
  let t : Γ(U.toScheme, ⊤) :=
    (((s ≫ E.hom) ≫ i1_freeSheafProjection U.toScheme k i).val.app (.op ⊤)
      (1 : Γ(U.toScheme, ⊤)))
  calc
    _ = Point.evaluate ⊤ t (ComplexPoint.asOpenPoint Q U x hx) := by
      rw [i1_conormalFrameCoordinates_sectionValue j k U E s x hx]
      exact i1_freeSectionSpecialization_coordinate (ComplexPoint.openScheme Q U) k
        (s ≫ E.hom) (ComplexPoint.asOpenPoint Q U x hx) i
    _ = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((ComplexPoint.liftToOpen Q U x hx).appTop t) :=
      ComplexPoint.evaluate_top_eq_appTop (X := ComplexPoint.openScheme Q U) t
        (ComplexPoint.asOpenPoint Q U x hx)
    _ = Point.evaluate U (normalFrameSectionCoefficient j k U E s i) x := by
      have h := i1_openRegularEvaluation U (U.topIso.hom t) x hx
      simpa only [Iso.hom_inv_id_apply, normalFrameSectionCoefficient, t] using h

theorem normalFrameSectionCoefficient_analyticAt_inverseChart (n : ℕ)
    [SmoothOfRelativeDimension n Q.hom]
    (z : ComplexPoint Q) (w : Fin n → ℂ)
    (hw : w ∈ (ComplexPoint.localChart Q n z).target)
    (hU : (ComplexPoint.localChart Q n z).symm w ∈ Point.overOpen U) :
    AnalyticAt ℂ (fun u : Fin n → ℂ => fun i : Fin k =>
      Point.evaluate U (normalFrameSectionCoefficient j k U E s i)
        ((ComplexPoint.localChart Q n z).symm u)) w := by
  apply analyticAt_pi_iff.mpr
  intro i
  exact ComplexPoint.analyticAt_localChart_symm_evaluate Q n z hw U
    (normalFrameSectionCoefficient j k U E s i) hU

theorem normalFrameSectionCoefficient_contMDiffOn (n : ℕ)
    [SmoothOfRelativeDimension n Q.hom] [LocallyOfFiniteType Q.hom]
    [QuasiCompact Q.hom] [IsSeparated Q.hom] :
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin k → ℂ) ω
      (fun x : ComplexPoint Q => fun i : Fin k =>
        Point.evaluate U (normalFrameSectionCoefficient j k U E s i) x)
      (Point.overOpen U) := by
  apply contMDiffOn_pi_space.mpr
  intro i
  exact (Analytic.f4_isHolFun_iff_contMDiffOn Q n
    (fun x => Point.evaluate U (normalFrameSectionCoefficient j k U E s i) x)
    (Point.isOpen_overOpen U)).mp
      (Analytic.f4_isHolFun_evaluate Q U (normalFrameSectionCoefficient j k U E s i))

#print axioms normalFrameSectionCoefficient_evaluate
#print axioms normalFrameSectionCoefficient_analyticAt_inverseChart
#print axioms normalFrameSectionCoefficient_contMDiffOn

end HodgeLean.Foundations.TubularEuler

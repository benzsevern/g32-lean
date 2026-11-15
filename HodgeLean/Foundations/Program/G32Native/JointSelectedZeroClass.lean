import HodgeLean.Foundations.Program.G32Native.JointSelectedZeroGeometry
import HodgeLean.Foundations.Program.G32Native.CanonicalComponentClass

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
attribute [local instance] G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6
  G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10
  G32JointPrefix.inst11 G32JointPrefix.inst18

attribute [local instance] G32JointZeroGeometry.integralQ G32JointZeroGeometry.projectiveQ G32JointZeroGeometry.smoothQ

/-- Supply the normalized class on this same zero-pair component. -/
theorem jointSelectedZeroClass_exists
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (U : G32JointZeroGeometry R) :
    ∃ c, a3b4_IsCycleClass R.W₀.hom (s2e_componentCycle U.ι ℚ) R.P.k c := by
  letI : Smooth U.Q.hom := SmoothOfRelativeDimension.smooth R.P.k U.Q.hom
  letI := U.immersion
  exact g32n_canonical_component_class R.Z R.B₀ R.W₀ U.Q R.hdimZ R.h R.P.k
    R.hselected R.γ R.hγsurj R.β₀ U.etale U.eQ U.ι

/-- Supply U17's conormal frames for the same immersion. -/
theorem jointSelectedZeroFrames
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (U : G32JointZeroGeometry R) :
    ∀ x : U.Q.left, ∃ V : U.Q.left.Opens, x ∈ V ∧
      Nonempty (Scheme.Modules.restrict (s2c_conormal U.ι.left) V.ι ≅
        (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin R.P.k) : V.toScheme.Modules)) := by
  letI : Smooth U.Q.hom := SmoothOfRelativeDimension.smooth R.P.k U.Q.hom
  letI := U.immersion
  exact g32n_canonical_conormal_frames R.Z R.B₀ R.W₀ U.Q R.hdimZ R.h R.P.k
    R.hselected R.γ R.hγsurj R.β₀ U.etale U.eQ U.ι

#print axioms jointSelectedZeroClass_exists
#print axioms jointSelectedZeroFrames
end HodgeLean.Foundations.Program

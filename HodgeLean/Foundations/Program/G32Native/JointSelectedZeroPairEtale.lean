import HodgeLean.Foundations.Program.G32Native.ZeroPairPowerEtale
import HodgeLean.Foundations.Program.G32Native.JointSelectedPrefix

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29

/-- Specialize the empty-branch étale supplier to the shared selected quotient. -/
theorem jointSelectedZeroPair_etale
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S)
    (hEmpty : g32p_exponents S = []) : Etale R.β₀.left := by
  exact g32w09_power_etale S R.Y R.Z R.W₀ R.B₀ R.a R.e R.ha1 R.hamul R.hinj
    R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.y R.hbranch
    R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀
    R.d₀ R.hd₀ R.hgenerator hEmpty

#print axioms jointSelectedZeroPair_etale
end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNStepAssembly
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNComparisonMono
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNHyperplaneCokernel
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalAlgebra
import HodgeLean.Foundations.Program.G32Native.PairedResidualTowerRestrictions

/-! # Single-pair conormal modification in the full ambient -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29

/-- The natural conormal comparison is an elementary modification with
untwisted quotient on the pair's own reduced hyperplane. Local frames
refer to the full ambient, including intersections with other pairs.
Source: Hartshorne, Algebraic Geometry, II.7.17.3 and II.8.17;
Fulton, Intersection Theory, Appendix B.6.
Open: the normalized residual-intersection conormal trivialization. -/
theorem paired_c3_route_n_step_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 < R.r) :
    ∃ E : ShortComplex (pairedC3Proj R.P.k).Modules,
      E.ShortExact ∧ E.X₂.IsQuasicoherent ∧
      (∀ x : pairedC3Proj R.P.k, ∃ U : (pairedC3Proj R.P.k).Opens, x ∈ U ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj E.X₂ ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin R.P.k) :
            U.toScheme.Modules))) ∧
      ∃ (e₁ : E.X₁ ≅ pairedC3StageConormal P i.castSucc)
        (e₂ : E.X₂ ≅ pairedC3StageConormal P i.succ),
        E.f ≫ e₂.hom = e₁.hom ≫ pairedC3StageComparison P i ∧
        Nonempty (E.X₃ ≅ pairedC3HyperplaneQuotient R.P.k (P.C.residue.indices i)) := by
  letI : Mono (pairedC3StageComparison P i) := paired_c3_route_n_comparison_mono_aux R P i hi
  obtain ⟨e⟩ := paired_c3_route_n_hyperplane_cokernel_aux R P i hi
  exact paired_c3_route_n_step_of_cokernel R P i e

end HodgeLean.Foundations.Program.G32Native

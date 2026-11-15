import HodgeLean.Foundations.Program.G32Native.PairedC3StageFrames
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Cokernel assembly for the natural retained-stage comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29

/-- The categorical sequence uses the original comparison as its first arrow.
The geometric inputs are precisely its injectivity and its actual cokernel. -/
theorem paired_c3_route_n_step_of_cokernel
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) [Mono (pairedC3StageComparison P i)]
    (e : cokernel (pairedC3StageComparison P i) ≅
      pairedC3HyperplaneQuotient R.P.k (P.C.residue.indices i)) :
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
  let E := ShortComplex.cokernelSequence (pairedC3StageComparison P i)
  have hE : E.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := by change Mono (pairedC3StageComparison P i); infer_instance
      epi_g := by change Epi (cokernel.π (pairedC3StageComparison P i)); infer_instance }
  refine ⟨E, hE,
    paired_c3_stage_conormal_quasicoherent R P i.succ,
    paired_c3_stage_conormal_frames R P i.succ, Iso.refl _, Iso.refl _, ?_, ⟨e⟩⟩
  exact Category.comp_id _ |>.trans (Category.id_comp _).symm

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import HodgeLean.Foundations.Program.G32Native.PairedResidualSliceFrames

/-! # Local conormal frames at every actual retained stage -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22
  G32JointBase.inst23 G32JointBase.inst24

/-- Each actual stage conormal has local rank-k frames on polynomial Proj.
This uses smoothness in the full retained ambient and no Route N step.
Source: Hartshorne, Algebraic Geometry, II.8, Theorem 8.17. -/
theorem paired_c3_stage_conormal_frames
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin (R.r + 1)) (x : pairedC3Proj R.P.k) :
    ∃ U : (pairedC3Proj R.P.k).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (pairedC3StageConormal P i) ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin R.P.k) : U.toScheme.Modules)) := by
  letI := P.C.residue.curve
  letI : IsClosedImmersion (P.C.slices i).left := P.C.sliceImmersion i
  let γ : g3_power R.Z (2 * R.P.k) ⟶ R.B₀ :=
    eqToHom (congrArg (g3_power R.Z) R.hselected.symm) ≫ R.γ
  letI : IsFinite γ.left := by
    dsimp only [γ, Over.comp_left]
    infer_instance
  have hsurj : Function.Surjective (Point.map γ) := by
    obtain ⟨_, h, _⟩ := s2e_symmetric_quotient_reindex R.Z R.B₀
      (R.h + 1) (2 * R.P.k) R.hselected.symm R.γ R.hγinv R.hγsurj R.hγ
    exact h
  let e := s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))
  let M := s2c_conormal (P.C.slices i).left
  obtain ⟨U, hx, ⟨eU⟩⟩ := paired_retained_slice_conormal_frames R.Z R.B₀ R.P.k R.r
    γ hsurj P.T.B P.T.e₀ P.T.b P.T.D P.T.hcartier P.T.hblowup i (P.C.slices i) (e.hom x)
  let ef : SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin R.P.k) ≅
      (Scheme.Modules.pullback U.ι).obj M :=
    eU.symm ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  exact ⟨e.hom ⁻¹ᵁ U, hx, ⟨(paired_module_framePullbackIso e.hom M U (Fin R.P.k) ef).symm⟩⟩

#print axioms paired_c3_stage_conormal_frames
/-- The actual stage conormal is locally free, independently of the
open single-pair exact-sequence construction. -/
theorem paired_c3_stage_conormal_locallyFree
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin (R.r + 1)) : (pairedC3StageConormal P i).IsLocallyFree := by
  apply paired_module_locallyFree_of_pullbackFrames
  intro x
  obtain ⟨U, hx, ⟨eU⟩⟩ := paired_c3_stage_conormal_frames R P i x
  exact ⟨U, hx, Fin R.P.k, ⟨eU.symm⟩⟩

#print axioms paired_c3_stage_conormal_locallyFree
/-- Quasicoherence of the actual stage conormal follows from its frames. -/
theorem paired_c3_stage_conormal_quasicoherent
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin (R.r + 1)) : (pairedC3StageConormal P i).IsQuasicoherent := by
  letI := paired_c3_stage_conormal_locallyFree R P i
  infer_instance

#print axioms paired_c3_stage_conormal_quasicoherent
end HodgeLean.Foundations.Program.G32Native

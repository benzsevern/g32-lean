import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateNormalization
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedMarkedRuling
import HodgeLean.Foundations.Program.G32Native.PairedC3RulingIdealTransport
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedLastLciComparison
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNComponentNoncontainment
import HodgeLean.Foundations.Program.SchoenTowerFibreTopology
noncomputable section
set_option maxRecDepth 4000
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
namespace ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24
attribute [local instance] G32JointComponent.h_T20_slice_immersion
attribute [local instance] G32JointComponent.hQ

/-- The selected final-stage ideal, local frames and marked ruling use one map.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_selected_final_geometry
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r) :
    ∃ σ : (P.T.B (Fin.last R.r)).left ⟶ (P.T.B i.castSucc).left,
      let I := (P.C.slices i.castSucc).left.ker.comap σ
      let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
      let M := K.comap σ ⊔ I
      I = P.C.ℓ.left.ker ⊓ M ∧
      (∀ x : I.subscheme, ∃ U : I.subscheme.Opens,
        x ∈ U ∧ IsAffine U.toScheme ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj (s2c_conormal I.subschemeι) ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin R.P.k) :
            U.toScheme.Modules))) ∧
      (¬ Set.range P.C.ℓ.left ⊆ (M.support : Set _)) ∧
      M.comap P.C.ℓ.left =
        s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i) ∧
      ∃ g : G32Native.residualComponent (V := P.T.B (Fin.last R.r)) M ⟶
          AlgebraicGeometry.RamifiedNormalization.StageFour.projectiveLine,
        Smooth g.left ∧ CategoryTheory.IsPullback
          (G32Native.residualIntersection P.C.ℓ M).hom
          (G32Native.residualIntersectionSecond P.C.ℓ M).left
          (AlgebraicGeometry.RamifiedNormalization.StageFour.projectiveLineChart
            1 (1 : ℂ)).left g.left := by
  have hs : i.succ = Fin.last R.r := Fin.ext hi
  have frames := paired_c3_selected_total_transform_frames R P i hi
  have identity := pairedC3_selected_last_total_transform R P i hi
  have ruling := pairedC3_selected_marked_ruling R P i hi
  have restriction := pairedC3_selected_residual_restriction R P.T P.W P.eFinal P.C i
  have hn := G32Native.paired_c3_route_n_component_noncontainment R P i
  have hdata : ∃ σ : (P.T.B i.succ).left ⟶ (P.T.B i.castSucc).left,
      let I := (P.C.slices i.castSucc).left.ker.comap σ
      let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
      let M := K.comap σ ⊔ I
      I = (P.C.slices i.succ).left.ker ⊓ M ∧
      (∀ x : I.subscheme, ∃ U : I.subscheme.Opens,
        x ∈ U ∧ IsAffine U.toScheme ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj (s2c_conormal I.subschemeι) ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin R.P.k) :
            U.toScheme.Modules))) ∧
      (¬ Set.range (P.C.slices i.succ).left ⊆ (M.support : Set _)) ∧
      M.comap (P.C.slices i.succ).left =
        s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i) ∧
      ∃ g : G32Native.residualComponent (V := P.T.B i.succ) M ⟶
          AlgebraicGeometry.RamifiedNormalization.StageFour.projectiveLine,
        Smooth g.left ∧ CategoryTheory.IsPullback
          (G32Native.residualIntersection (P.C.slices i.succ) M).hom
          (G32Native.residualIntersectionSecond (P.C.slices i.succ) M).left
          (AlgebraicGeometry.RamifiedNormalization.StageFour.projectiveLineChart
            1 (1 : ℂ)).left g.left := by
    refine ⟨(P.T.b i).left, identity, frames, hn, restriction, ?_⟩
    exact G32Native.paired_ruling_of_ideal_eq (P.C.slices i.succ) _ _
      (Scheme.IdealSheafData.comap_sup _ _ _) _ ruling
  rw [hs, P.C.sliceLast] at hdata
  exact hdata

#print axioms paired_c3_selected_final_geometry
end ResidueSelected
end HodgeLean.Foundations.Program

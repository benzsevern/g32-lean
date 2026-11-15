import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedFinalGeometry
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

/-- The actual residual union carries the selected frames, pullback and ruling.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_selected_final_union_geometry
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
      ∃ p : (G32Native.residualUnion P.C.ℓ M).left ⟶
          ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ),
      ∃ sq : CategoryTheory.IsPullback p (G32Native.residualUnionι P.C.ℓ M).left
          (P.C.slices i.castSucc).left σ,
      (∀ x : (G32Native.residualUnion P.C.ℓ M).left,
        ∃ U : (G32Native.residualUnion P.C.ℓ M).left.Opens,
          x ∈ U ∧ IsAffine U.toScheme ∧
          Nonempty ((Scheme.Modules.pullback U.ι).obj
            (s2c_conormal (G32Native.residualUnionι P.C.ℓ M).left) ≅
            (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin R.P.k) :
              U.toScheme.Modules))) ∧
      (¬ (P.C.ℓ.left.ker.support : Set (P.T.B (Fin.last R.r)).left) ⊆
        (M.support : Set (P.T.B (Fin.last R.r)).left)) ∧
      M.comap P.C.ℓ.left = s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i) ∧
      ∃ g : G32Native.residualComponent (V := P.T.B (Fin.last R.r)) M ⟶
          AlgebraicGeometry.RamifiedNormalization.StageFour.projectiveLine,
        Smooth g.left ∧ CategoryTheory.IsPullback
          (G32Native.residualIntersection P.C.ℓ M).hom
          (G32Native.residualIntersectionSecond P.C.ℓ M).left
          (AlgebraicGeometry.RamifiedNormalization.StageFour.projectiveLineChart
            1 (1 : ℂ)).left g.left := by
  obtain ⟨σ, hI, hframes, hn, hJ, g, hsm, sq₂⟩ :=
    paired_c3_selected_final_geometry R P i hi
  dsimp only at hI hframes hn hJ
  let I := (P.C.slices i.castSucc).left.ker.comap σ
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let M := K.comap σ ⊔ I
  letI := P.C.sliceImmersion i.castSucc
  obtain ⟨p, sq⟩ := G32Native.paired_last_total_transform_pullback P.C.ℓ M
    (P.C.slices i.castSucc).left σ hI
  refine ⟨σ, p, sq, ?_, ?_, hJ, g, hsm, sq₂⟩
  · rw [hI] at hframes
    exact hframes
  · intro hsub
    exact hn (P.C.ℓ.left.range_subset_ker_support.trans hsub)

#print axioms paired_c3_selected_final_union_geometry
end ResidueSelected
end HodgeLean.Foundations.Program

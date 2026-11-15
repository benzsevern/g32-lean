import HodgeLean.Foundations.Program.SchoenCycleS3AffinePullback
import HodgeLean.Foundations.Program.G32Native.PairedC3PullbackSections

/-! # Original generators under the affine pullback comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The affine comparison carries the original pulled-back associated
section to the associated section of its scalar-extension unit tensor. -/
theorem paired_c3_affine_pullback_tilde_unit
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (M : ModuleCat R) (x : M) :
    ((s2e_affinePullbackTildeIso φ).hom.app M).app ⊤
      (pairedC3PullbackSection (Spec.map φ) (tilde M) ⊤
        ((tilde.adjunction (R := R)).unit.app M x)) =
    (tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M x) := by
  let a := ((tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
      (s2e_affinePushforwardGammaIso φ)
  let b := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))
  have h := Adjunction.unit_leftAdjointUniq_hom_app a b M
  exact congrArg (fun f => f x) h

#print axioms paired_c3_affine_pullback_tilde_unit
end HodgeLean.Foundations.Program.G32Native

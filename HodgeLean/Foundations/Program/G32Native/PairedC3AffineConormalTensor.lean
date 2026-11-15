import HodgeLean.Foundations.Program.G32Native.PairedC3AffineIdealGenerator
import HodgeLean.Foundations.Program.G32Native.PairedC3AffinePullbackUnit

/-! # Original affine conormal classes in the scalar-extension comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The actual affine conormal as the associated scalar extension of its
original ring kernel, using the natural ideal-section identification. -/
def pairedC3AffineConormalTensorIso (R S : CommRingCat.{0}) (p : R ⟶ S) :
    Conormal.sheaf (Spec.map p) ≅
      tilde ((ModuleCat.extendScalars p.hom).obj (ModuleCat.of R (RingHom.ker p.hom))) :=
  (Scheme.Modules.pullback (Spec.map p)).mapIso (Conormal.affineIdealIso R S p) ≪≫
    (s2e_affinePullbackTildeIso p).app (ModuleCat.of R (RingHom.ker p.hom))

/-- The canonical conormal class maps to the unit tensor of its original
kernel element, with no choice of an unlabelled affine frame. -/
theorem paired_c3_affine_conormal_tensor_generator
    (R S : CommRingCat.{0}) (p : R ⟶ S)
    (x : (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule (Spec.map p))) :
    (pairedC3AffineConormalTensorIso R S p).hom.app ⊤
      (pairedC3PullbackSection (Spec.map p) (Conormal.idealModule (Spec.map p)) ⊤ x) =
    (tilde.adjunction (R := S)).unit.app
      ((ModuleCat.extendScalars p.hom).obj (ModuleCat.of R (RingHom.ker p.hom)))
      ((ModuleCat.extendRestrictScalarsAdj p.hom).unit.app
        (ModuleCat.of R (RingHom.ker p.hom)) (s2e_affine_ideal_sections_equiv R S p x)) := by
  change ((s2e_affinePullbackTildeIso p).hom.app
    (ModuleCat.of R (RingHom.ker p.hom))).app ⊤
      (((Scheme.Modules.pullback (Spec.map p)).map (Conormal.affineIdealIso R S p).hom).app ⊤
        (pairedC3PullbackSection (Spec.map p) (Conormal.idealModule (Spec.map p)) ⊤ x)) = _
  let q := (s2e_affinePullbackTildeIso p).hom.app (ModuleCat.of R (RingHom.ker p.hom))
  let x' : Γ(Conormal.idealModule (Spec.map p), ⊤) := x
  have hn := paired_c3_pullback_section_naturality (Spec.map p)
    (Conormal.idealModule (Spec.map p)) (Conormal.affineIdealIso R S p).hom ⊤ x'
  have hn' := congrArg (fun z => q.app ⊤ z) hn.symm
  have hi := paired_c3_affine_ideal_generator_section R S p x
  have hi' := congrArg (fun z => q.app ⊤
    (pairedC3PullbackSection (Spec.map p)
      (tilde (ModuleCat.of R (RingHom.ker p.hom))) ⊤ z)) hi
  exact hn'.trans (hi'.trans (paired_c3_affine_pullback_tilde_unit R S p _ _))

#print axioms paired_c3_affine_conormal_tensor_generator
end HodgeLean.Foundations.Program.G32Native

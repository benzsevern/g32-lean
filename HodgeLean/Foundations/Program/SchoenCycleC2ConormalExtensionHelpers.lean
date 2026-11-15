import HodgeLean.Foundations.Program.SchoenCycleC2ConormalAffineHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2AffineIdealKernelHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ScalarExtensionTensorHelpers
import Mathlib.RingTheory.Extension.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual conormal sheaf of an affine algebra extension is the
associated sheaf of its algebraic conormal module. -/
def s2e_affine_extension_conormal_iso
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{0} R S) :
    s2c_conormal (Spec.map (CommRingCat.ofHom (algebraMap P.Ring S))) ≅
      tilde (ModuleCat.of S P.Cotangent) := by
  let φ : CommRingCat.of P.Ring ⟶ CommRingCat.of S :=
    CommRingCat.ofHom (algebraMap P.Ring S)
  let eI := s2e_affine_ideal_sections_equiv (CommRingCat.of P.Ring) (CommRingCat.of S) φ
  exact s2e_affine_conormal_sections_iso _ _ φ ≪≫
    (tilde.functor (CommRingCat.of S)).mapIso
      ((ModuleCat.extendScalars φ.hom).mapIso eI.toModuleIso ≪≫
        s2e_extendScalars_algebraMap_iso (ModuleCat.of P.Ring P.ker) ≪≫
        P.cotangentEquiv.toModuleIso)

end HodgeLean.Foundations.Program

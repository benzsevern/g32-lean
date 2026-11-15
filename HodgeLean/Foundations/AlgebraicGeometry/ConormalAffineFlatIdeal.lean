import HodgeLean.Foundations.AlgebraicGeometry.ConormalFlatIdeal
import HodgeLean.Foundations.AlgebraicGeometry.ConormalFramesDefs
import HodgeLean.Foundations.Program.SchoenCycleC2AffineIdealKernelHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2AffinePullbackHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ScalarExtensionTensorHelpers

/-! # Flat affine transport of kernel ideal modules
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Foundations.Program

namespace AlgebraicGeometry.Conormal

/-- The kernel-defined ideal of an affine morphism is the associated kernel module. -/
def affineIdealIso (R A : CommRingCat.{0}) (p : R ⟶ A) :
    idealModule (Spec.map p) ≅ tilde (ModuleCat.of R (RingHom.ker p.hom)) := by
  let M := idealModule (Spec.map p)
  haveI : IsIso M.fromTildeΓ := s2e_idealModule_spec_fromTilde_isIso R (Spec.map p)
  exact (asIso M.fromTildeΓ).symm ≪≫
    (tilde.functor R).mapIso (s2e_affine_ideal_sections_equiv R A p).toModuleIso

/-- Flat pullback of an associated ideal module is the associated extended ideal. -/
def affineFlatIdealIso
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal R) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
        (tilde (ModuleCat.of R I)) ≅
      tilde (ModuleCat.of S (I.map (algebraMap R S))) :=
  (s2e_affine_pullback_tilde_iso (CommRingCat.of R) (CommRingCat.of S)
    (CommRingCat.ofHom (algebraMap R S))).app (ModuleCat.of R I) ≪≫
    (tilde.functor (CommRingCat.of S)).mapIso
      (s2e_extendScalars_algebraMap_iso (ModuleCat.of R I) ≪≫
        (idealExtensionEquiv (S := S) I).toModuleIso)

/-- Affine kernel ideals transport along flat scalar extension when the ring kernels agree. -/
def affineFlatKernelIdealIso
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (h : (RingHom.ker p.hom).map (algebraMap R S) = RingHom.ker q.hom) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
        (idealModule (Spec.map p)) ≅ idealModule (Spec.map q) :=
  (Scheme.Modules.pullback _).mapIso (affineIdealIso _ _ p) ≪≫
    affineFlatIdealIso (RingHom.ker p.hom) ≪≫
    (tilde.functor (CommRingCat.of S)).mapIso
      (LinearEquiv.ofEq _ _ h).toModuleIso ≪≫
    (affineIdealIso _ _ q).symm

end AlgebraicGeometry.Conormal

import HodgeLean.Foundations.Program.SchoenCycleS3AffineKernelSheaf
import HodgeLean.Foundations.Program.SchoenCycleS3CotangentPullback

/-! # The ideal module on an affine quotient -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Global sections of the ideal module of an affine morphism identify its ring kernel. -/
def s2e_affineIdealModuleGammaIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    moduleSpecΓFunctor.obj (s2c_idealModule (Spec.map f)) ≅
      ModuleCat.of R (RingHom.ker f.hom) := by
  letI := f.hom.toAlgebra
  let F := moduleSpecΓFunctor (R := R)
  let g := SheafOfModules.unitToPushforwardObjUnit (Spec.map f).toRingCatSheafHom
  let l : ModuleCat.of R R ⟶ (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of S S) :=
    ModuleCat.ofHom (Algebra.linearMap R S)
  let a : F.obj (SheafOfModules.unit (Spec R).ringCatSheaf) ≅ ModuleCat.of R R :=
    (tilde.isoTop (ModuleCat.of R R)).symm
  let b : F.obj ((Scheme.Modules.pushforward (Spec.map f)).obj
      (SheafOfModules.unit (Spec S).ringCatSheaf)) ≅
      (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of S S) :=
    (s2e_affinePushforwardGammaIso f).app _ ≪≫
      (ModuleCat.restrictScalars f.hom).mapIso (tilde.isoTop (ModuleCat.of S S)).symm
  letI : F.IsRightAdjoint := (tilde.adjunction (R := R)).isRightAdjoint
  letI : F.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  refine PreservesKernel.iso F g ≪≫ kernel.mapIso (F.map g) l a b ?_ ≪≫
    ModuleCat.kernelIsoKer l
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv r) =
    (Scheme.ΓSpecIso S).inv (f r)
  exact congrArg (fun q : R ⟶ Γ(Spec S, ⊤) => q r)
    (Scheme.ΓSpecIso_inv_naturality f).symm

/-- The actual ideal module of an affine morphism is the sheaf associated to its ring kernel. -/
def s2e_affineIdealModuleIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    s2c_idealModule (Spec.map f) ≅ tilde (ModuleCat.of R (RingHom.ker f.hom)) := by
  letI := s2e_affineIdealModule_fromTildeGamma f
  exact (asIso (s2c_idealModule (Spec.map f)).fromTildeΓ).symm ≪≫
    (tilde.functor R).mapIso (s2e_affineIdealModuleGammaIso f)

/-- The quotient immersion has the associated ideal as its actual ideal module. -/
def s2e_affineQuotientIdealModuleIso {R : CommRingCat.{u}} (I : Ideal R) :
    s2c_idealModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      tilde (ModuleCat.of R I) :=
  s2e_affineIdealModuleIso (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≪≫
    (tilde.functor R).mapIso
      ((LinearEquiv.ofEq _ _ (Ideal.mk_ker (I := I))).toModuleIso)

/-- The kernel-and-pullback conormal of a quotient immersion is the associated cotangent sheaf. -/
def s2e_affineQuotientConormalIso {R : CommRingCat.{u}} (I : Ideal R) :
    s2c_conormal (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      tilde (ModuleCat.of (CommRingCat.of (R ⧸ I)) I.Cotangent) :=
  (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapIso
      (s2e_affineQuotientIdealModuleIso I) ≪≫
    s2e_tildeIdealPullbackCotangentIso I

end HodgeLean.Foundations.Program

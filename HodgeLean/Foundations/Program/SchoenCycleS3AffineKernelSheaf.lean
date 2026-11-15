import HodgeLean.Foundations.Program.SchoenCycleS3KernelLocalizing
import HodgeLean.Foundations.Program.SchoenCycleS3AffinePullback
import HodgeLean.Foundations.Program.SchoenCycleS3IdealModuleSections

/-! # Affine module kernels and associated sheaves -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The affine change from structure-sheaf modules to constant-ring modules preserves kernels. -/
theorem s2e_affineModuleKernelComparison {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (g : M ⟶ N) :
    PreservesLimit (parallelPair g 0) (modulesSpecToSheaf (R := R)) := by
  let F := modulesSpecToSheaf (R := R)
  let G := TopCat.Sheaf.forget (ModuleCat R) (Spec R)
  let : PreservesLimit (parallelPair g 0) (F ⋙ G) := by
    apply preservesLimit_of_evaluation
    intro U
    let a : R →+* Γ(Spec R, U.unop) :=
      ((Spec R).presheaf.map U.unop.leTop.op).hom.comp (Scheme.ΓSpecIso R).inv.hom
    change PreservesLimit (parallelPair g 0)
      (SheafOfModules.evaluation (Spec R).ringCatSheaf U ⋙ ModuleCat.restrictScalars a)
    let : PreservesLimit (parallelPair g 0)
        (SheafOfModules.evaluation (Spec R).ringCatSheaf U) :=
      SheafOfModules.evaluationPreservesLimit
        (parallelPair (C := SheafOfModules (Spec R).ringCatSheaf) g 0) U
    apply comp_preservesLimit
  exact preservesLimit_of_reflects_of_preserves F G

/-- The module kernel is localizing whenever both affine module sheaves are localizing. -/
theorem s2e_affineModuleKernel_isLocalizing {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (g : M ⟶ N)
    (hM : IsLocalizing (modulesSpecToSheaf.obj M))
    (hN : IsLocalizing (modulesSpecToSheaf.obj N)) :
    IsLocalizing (modulesSpecToSheaf.obj (kernel g)) := by
  let F : (Spec R).Modules ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R) :=
    modulesSpecToSheaf
  let : F.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let : PreservesLimit (parallelPair g 0) F := s2e_affineModuleKernelComparison g
  let e := PreservesKernel.iso F g
  have hk := s2e_sheafKernel_isLocalizing (F.map g) hM hN
  exact (isLocalizing_iff_of_iso
    (show (modulesSpecToSheaf.obj (kernel g)) ≅
      (show TopCat.Sheaf (ModuleCat R) (Spec R) from
        (kernel (F.map g) : CategoryTheory.Sheaf
          (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R))) from e)).mpr hk

/-- The ideal module of an affine morphism is associated to its global sections. -/
theorem s2e_affineIdealModule_fromTildeGamma {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsIso (s2c_idealModule (Spec.map f)).fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff_isLocalizing]
  exact s2e_affineModuleKernel_isLocalizing
    (SheafOfModules.unitToPushforwardObjUnit (Spec.map f).toRingCatSheafHom)
    (isLocalizing_tilde (ModuleCat.of R R))
    (isLocalizing_pushforward_of_isLocalizing f (isLocalizing_tilde (ModuleCat.of S S)))

end HodgeLean.Foundations.Program

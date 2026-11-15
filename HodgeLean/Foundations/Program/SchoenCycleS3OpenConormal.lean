import HodgeLean.Foundations.Program.SchoenCycleS3AffineIdealCotangent
import HodgeLean.Foundations.Program.SchoenCycleS3RestrictionKernels

/-! # Open restriction of immersion ideal modules -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Restricting the direct image of the structure module agrees with the restricted morphism. -/
def s2e_restrictPushforwardUnitIso {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.restrict
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj
        (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun V => ?_) ?_
  · let e := X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U V.unop)).op
    refine ModuleCat.isoMk ((forget₂ CommRingCat RingCat ⋙ forget₂ _ Ab).mapIso e) ?_
    intro r
    ext x
    let x' : Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ V.unop)) := x
    let r' : Γ(Y, U.ι ''ᵁ V.unop) := (U.ι.appIso V.unop).inv r
    change (show Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V.unop)) from
        (f ∣_ U).app V.unop r) * e.hom x' = e.hom (f.app (U.ι ''ᵁ V.unop) r' * x')
    dsimp only [r']
    rw [Scheme.Opens.ι_appIso]
    rw [map_mul]
    congr 1
    exact congrArg (fun q => q r) (morphismRestrict_app f U V.unop)
  · intro V W h
    ext x
    change (X.presheaf.map
        ((Opens.map f.base).map (U.ι.opensFunctor.map h.unop)).op ≫
      X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op) x =
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op ≫
        X.presheaf.map (((f ⁻¹ᵁ U).ι.opensFunctor).map
          ((Opens.map (f ∣_ U).base).map h.unop)).op) x
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 2

/-- The restricted direct-image comparison respects the structure-module map. -/
@[reassoc]
theorem s2e_restrictPushforwardUnitIso_unit {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      (s2e_restrictPushforwardUnitIso f U).hom =
    (Scheme.Modules.restrictUnitIso U.ι).hom ≫
      SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op
      (f.app (U.ι ''ᵁ V.unop) r) =
    (f ∣_ U).app V.unop ((U.ι.appIso V.unop).hom r)
  rw [Scheme.Opens.ι_appIso]
  exact congrArg (fun q => q r) (morphismRestrict_app f U V.unop).symm

/-- The ideal module commutes with restriction to an open subscheme of the ambient scheme. -/
def s2e_restrictIdealModuleIso {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.restrict (s2c_idealModule f) U.ι ≅ s2c_idealModule (f ∣_ U) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let g := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let g' := SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom
  let : PreservesLimit (parallelPair g 0) F := s2e_restrictFunctor_preservesKernel U.ι g
  let : F.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  exact PreservesKernel.iso F g ≪≫ kernel.mapIso (F.map g) g'
    (Scheme.Modules.restrictUnitIso U.ι) (s2e_restrictPushforwardUnitIso f U)
    (s2e_restrictPushforwardUnitIso_unit f U)

/-- The actual conormal commutes with restriction to an ambient open subscheme. -/
def s2e_restrictConormalIso {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.restrict (s2c_conormal f) (f ⁻¹ᵁ U).ι ≅
      s2c_conormal (f ∣_ U) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app (s2c_conormal f) ≪≫
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app (s2c_idealModule f) ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app (s2c_idealModule f) ≪≫
    (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm.app (s2c_idealModule f) ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (s2c_idealModule f)).symm ≪≫
        s2e_restrictIdealModuleIso f U)

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCycleS3OpenConormal

/-! # Isomorphism transport for immersion conormals -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An isomorphism induces an isomorphism on the structure-module direct image. -/
theorem s2e_unitPushforward_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  change IsIso (((forget₂ CommRingCat RingCat) ⋙ forget₂ RingCat Ab).map (f.app U))
  infer_instance

/-- The structure-module map respects composition of scheme morphisms. -/
@[reassoc]
theorem s2e_unitPushforward_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf) =
    SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change f.app (g ⁻¹ᵁ U.unop) (g.app U.unop r) = (f ≫ g).app U.unop r
  exact congrArg (fun q => q r) (Scheme.Hom.comp_app f g U.unop).symm

/-- Changing the source by an isomorphism preserves the immersion ideal module. -/
def s2e_sourceIsoIdealModuleIso {X' X Y : Scheme} (m : X' ⟶ X) [IsIso m] (f : X ⟶ Y) :
    s2c_idealModule (m ≫ f) ≅ s2c_idealModule f := by
  let g := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let g' := SheafOfModules.unitToPushforwardObjUnit (m ≫ f).toRingCatSheafHom
  let gm := SheafOfModules.unitToPushforwardObjUnit m.toRingCatSheafHom
  letI : IsIso gm := s2e_unitPushforward_isIso m
  let b := (Scheme.Modules.pushforwardComp m f).symm.app
      (SheafOfModules.unit X'.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward f).mapIso (asIso gm).symm
  refine kernel.mapIso g' g (Iso.refl _) b ?_
  rw [← Iso.eq_comp_inv]
  exact (s2e_unitPushforward_comp m f).symm

/-- Pullback along a source isomorphism transports the actual conormal. -/
def s2e_sourceIsoConormalIso {X' X Y : Scheme} (m : X' ⟶ X) [IsIso m] (f : X ⟶ Y) :
    (Scheme.Modules.pullback m).obj (s2c_conormal f) ≅ s2c_conormal (m ≫ f) :=
  (Scheme.Modules.pullbackComp m f).app (s2c_idealModule f) ≪≫
    (Scheme.Modules.pullback (m ≫ f)).mapIso (s2e_sourceIsoIdealModuleIso m f).symm

/-- Direct image of an immersion ideal module respects a source-base isomorphism. -/
def s2e_ambientIsoIdealPushforwardIso {X Y Z : Scheme} (f : X ⟶ Y) (j : Y ⟶ Z) [IsIso j] :
    (Scheme.Modules.pushforward j).obj (s2c_idealModule f) ≅ s2c_idealModule (f ≫ j) := by
  let F := Scheme.Modules.pushforward j
  let g := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let g' := SheafOfModules.unitToPushforwardObjUnit (f ≫ j).toRingCatSheafHom
  let gj := SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom
  letI : IsIso gj := s2e_unitPushforward_isIso j
  refine PreservesKernel.iso F g ≪≫ kernel.mapIso (F.map g) g'
    (asIso gj).symm ((Scheme.Modules.pushforwardComp f j).app _) ?_
  rw [← Iso.inv_comp_eq]
  exact s2e_unitPushforward_comp f j

/-- Pullback recovers the immersion ideal module after an ambient isomorphism. -/
def s2e_ambientIsoIdealPullbackIso {X Y Z : Scheme} (f : X ⟶ Y) (j : Y ⟶ Z) [IsIso j] :
    (Scheme.Modules.pullback j).obj (s2c_idealModule (f ≫ j)) ≅ s2c_idealModule f :=
  (Scheme.Modules.pullback j).mapIso (s2e_ambientIsoIdealPushforwardIso f j).symm ≪≫
    ((Functor.isoWhiskerLeft (Scheme.Modules.pushforward j)
      (Scheme.Modules.restrictFunctorIsoPullback j).symm) ≪≫
        Scheme.Modules.restrictFunctorAdjCounitIso j).app (s2c_idealModule f)

/-- An ambient isomorphism preserves the actual conormal. -/
def s2e_ambientIsoConormalIso {X Y Z : Scheme} (f : X ⟶ Y) (j : Y ⟶ Z) [IsIso j] :
    s2c_conormal (f ≫ j) ≅ s2c_conormal f :=
  (Scheme.Modules.pullbackComp f j).symm.app (s2c_idealModule (f ≫ j)) ≪≫
    (Scheme.Modules.pullback f).mapIso (s2e_ambientIsoIdealPullbackIso f j)

/-- A commuting square of scheme isomorphisms transports actual conormals. -/
def s2e_conormalArrowIso {X' X Y' Y : Scheme}
    (m : X' ⟶ X) (j : Y' ⟶ Y) [IsIso m] [IsIso j]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (h : m ≫ f = f' ≫ j) :
    (Scheme.Modules.pullback m).obj (s2c_conormal f) ≅ s2c_conormal f' :=
  s2e_sourceIsoConormalIso m f ≪≫ eqToIso (congrArg s2c_conormal h) ≪≫
    s2e_ambientIsoConormalIso f' j

end HodgeLean.Foundations.Program

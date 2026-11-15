import HodgeLean.Foundations.Curves.Picard.LineBundles.IdealPullbackIsomorphism
import HodgeLean.Foundations.AlgebraicGeometry.ConormalIsoComparison
import HodgeLean.Foundations.Program.G32Native.PairedConormalPullbackUnit
import HodgeLean.Foundations.Curves.Picard.LineBundles.IdealModuleTransportIso

/-! # The actual ideal module under a specified scheme isomorphism -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A scheme isomorphism pulls the actual ideal module back to the
module of its actual comap ideal, through the natural ideal comparison. -/
def paired_idealPullbackIso_of_iso {X Y : Scheme.{0}} (e : X ≅ Y)
    (I : Y.IdealSheafData) :
    (Scheme.Modules.pullback e.hom).obj (Conormal.idealModule I.subschemeι) ≅
      Conormal.idealModule (I.comap e.hom).subschemeι := by
  let g := (I.comapIso e.hom).hom ≫ pullback.snd e.hom I.subschemeι
  have h : g ≫ I.subschemeι = (I.comap e.hom).subschemeι ≫ e.hom := by
    dsimp only [g]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, I.comapIso_hom_fst]
  letI : IsIso g := by dsimp only [g]; infer_instance
  letI := Conormal.idealPullbackMap_isIso_of_isIso I.subschemeι
    (I.comap e.hom).subschemeι e.hom g h
  exact asIso (Conormal.idealPullbackMap I.subschemeι (I.comap e.hom).subschemeι e.hom g h)

/-- The natural ideal-module isomorphism retains the original inclusion
into the canonically pulled-back structure module. -/
theorem paired_idealPullbackIso_of_iso_inclusion {X Y : Scheme.{0}} (e : X ≅ Y)
    (I : Y.IdealSheafData) :
    (paired_idealPullbackIso_of_iso e I).hom ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (I.comap e.hom).subschemeι.toRingCatSheafHom) =
      (Scheme.Modules.pullback e.hom).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)) ≫
          (paired_module_pullbackUnitIso e.hom).hom := by
  let g := (I.comapIso e.hom).hom ≫ pullback.snd e.hom I.subschemeι
  have h : g ≫ I.subschemeι = (I.comap e.hom).subschemeι ≫ e.hom := by
    dsimp only [g]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, I.comapIso_hom_fst]
  change Conormal.idealPullbackMap I.subschemeι (I.comap e.hom).subschemeι e.hom g h ≫ _ =
    (Scheme.Modules.pullback e.hom).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)) ≫
        SheafOfModules.pullbackObjUnitToUnit e.hom.toRingCatSheafHom
  exact Conormal.idealPullbackMap_inclusion I.subschemeι (I.comap e.hom).subschemeι e.hom g h

/-- Equality transport to a specified comap ideal retains the actual
structure-module inclusion of the natural ideal pullback isomorphism. -/
theorem paired_idealPullbackIso_transport_inclusion {X Y : Scheme.{0}} (e : X ≅ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (h : I.comap e.hom = J) :
    (HodgeLean.Foundations.Curves.Picard.LineBundles.idealModuleTransportIso h
      (paired_idealPullbackIso_of_iso e I)).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom) =
      (Scheme.Modules.pullback e.hom).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)) ≫
          (paired_module_pullbackUnitIso e.hom).hom := by
  exact (HodgeLean.Foundations.Curves.Picard.LineBundles.idealModuleTransportIso_inclusion h
    (paired_idealPullbackIso_of_iso e I)).trans (paired_idealPullbackIso_of_iso_inclusion e I)

/-- The actual pulled ideal has a specified module isomorphism to any
identified comap ideal, together with its original inclusion equation. -/
theorem paired_idealPullbackIso_exists_preserving_inclusion {X Y : Scheme.{0}} (e : X ≅ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (h : I.comap e.hom = J) :
    ∃ E : (Scheme.Modules.pullback e.hom).obj (Conormal.idealModule I.subschemeι) ≅
      Conormal.idealModule J.subschemeι,
      E.hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom) =
        (Scheme.Modules.pullback e.hom).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)) ≫
            (paired_module_pullbackUnitIso e.hom).hom := by
  refine ⟨HodgeLean.Foundations.Curves.Picard.LineBundles.idealModuleTransportIso h
    (paired_idealPullbackIso_of_iso e I), ?_⟩
  exact paired_idealPullbackIso_transport_inclusion e I J h


open HodgeLean.Foundations.Curves.Picard.LineBundles HodgeLean.Foundations.Program
/-- The actual comap ideal comparison is invertible along every scheme isomorphism. -/
theorem conormal_idealPullbackHom_isIso {X Y : Scheme} (f : Y ⟶ X) [IsIso f]
    (I : X.IdealSheafData) : IsIso (idealPullbackHom f I) := by
  let J := I.comap f
  let g := (I.comapIso f).hom ≫ pullback.snd f I.subschemeι
  have hg : IsIso g := by dsimp only [g]; infer_instance
  have hsq : g ≫ I.subschemeι = J.subschemeι ≫ f := by
    dsimp only [g, J]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, I.comapIso_hom_fst]
  have he : idealPullbackHom f I =
      Conormal.idealPullbackMap I.subschemeι J.subschemeι f g hsq := by
    apply (cancel_mono (kernel.ι
      (SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom))).mp
    rw [idealPullbackHom_inclusion, Conormal.idealPullbackMap_inclusion]
    rfl
  rw [he]
  exact Conormal.idealPullbackMap_isIso_of_isIso I.subschemeι J.subschemeι f g hsq


end HodgeLean.Foundations.Program.G32Native

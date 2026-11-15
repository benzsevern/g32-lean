import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitFreePullback
import HodgeLean.Foundations.Program.G32Native.PairedConormalGlobalSectionEvaluation
import Mathlib.CategoryTheory.Functor.EpiMono

/-! # Pullback of the actual supplied quotient and its ordered generators -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Curves.Picard.LineBundles

/-- Transport the supplied quotient through its canonical unit-plus-free source comparison. -/
def conormalPresentationPullback {X Y : Scheme.{0}} (f : X ⟶ Y) (k : ℕ)
    (M : Y.Modules)
    (π : (SheafOfModules.unit Y.ringCatSheaf ⊞
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) ⟶ M) :
    (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶
        (Scheme.Modules.pullback f).obj M :=
  (conormalUnitFreePullbackIso f k).inv ≫ (Scheme.Modules.pullback f).map π

/-- The actual supplied quotient stays an epimorphism after source transport. -/
theorem conormal_presentation_pullback_epi {X Y : Scheme.{0}} (f : X ⟶ Y) (k : ℕ)
    (M : Y.Modules)
    (π : (SheafOfModules.unit Y.ringCatSheaf ⊞
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) ⟶ M) [Epi π] :
    Epi (conormalPresentationPullback f k M π) := by
  let F := Scheme.Modules.pullback f
  letI : F.PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_adjunction
      (Scheme.Modules.pullbackPushforwardAdjunction f)
  letI : Epi (F.map π) := CategoryTheory.Functor.map_epi F π
  letI : Epi (conormalUnitFreePullbackIso f k).inv := inferInstance
  dsimp only [conormalPresentationPullback]
  infer_instance

/-- The transported quotient retains the actual composition with every
supplied relation arrow, through its canonical source comparison. -/
theorem conormal_presentation_pullback_comp {X Y : Scheme.{0}} (f : X ⟶ Y) (k : ℕ)
    (M : Y.Modules)
    (π : (SheafOfModules.unit Y.ringCatSheaf ⊞
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) ⟶ M)
    {L : Y.Modules}
    (r : L ⟶ (SheafOfModules.unit Y.ringCatSheaf ⊞
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin k))) :
    (Scheme.Modules.pullback f).map r ≫ (conormalUnitFreePullbackIso f k).hom ≫
      conormalPresentationPullback f k M π = (Scheme.Modules.pullback f).map (r ≫ π) := by
  simp only [conormalPresentationPullback, Category.assoc,
    Iso.hom_inv_id_assoc, CategoryTheory.Functor.map_comp]

#print axioms conormal_presentation_pullback_epi
#print axioms conormal_presentation_pullback_comp
end HodgeLean.Foundations.Program.G32Native

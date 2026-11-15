import HodgeLean.Foundations.Program.G32Native.PairedConormalProjectiveSpaceLift
import HodgeLean.Foundations.Program.G32Native.PairedConormalModelLocallyFree

/-! # Global lifting for the supplied smooth conormal model -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Smooth conormal geometry supplies the middle-object regularity needed for a global lift. -/
theorem paired_conormal_actual_unit_lift
    (Q : Over (Spec ↧ℂ)) (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (V : Scheme) (j : Q.left ⟶ V) [IsClosedImmersion j]
    (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) sV]
    (M D : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules)
    (E : s2c_conormal j ≅ (Scheme.Modules.pullback eQ.hom.left).obj M)
    (f : (SheafOfModules.free (Fin k) :
      (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules) ⟶ M)
    (g : M ⟶ D) (hfg : f ≫ g = 0) (hs : (ShortComplex.mk f g hfg).ShortExact)
    (u : SheafOfModules.unit
      (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).ringCatSheaf ⟶ D) :
    ∃ l : SheafOfModules.unit
      (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).ringCatSheaf ⟶ M, l ≫ g = u := by
  let ι : Q ⟶ Over.mk sV := Over.homMk j hj
  letI : IsClosedImmersion ι.left := ‹IsClosedImmersion j›
  letI : SmoothOfRelativeDimension (k + k) (Over.mk sV).hom :=
    ‹SmoothOfRelativeDimension (k + k) sV›
  let e := (Over.forget (Spec ↧ℂ)).mapIso eQ
  letI : M.IsLocallyFree := paired_smooth_conormal_model_locallyFree Q (Over.mk sV)
    k k ι _ e M E
  let S := ShortComplex.mk f g hfg
  letI : S.X₂.IsQuasicoherent := inferInstanceAs M.IsQuasicoherent
  exact conormal_projectiveSpace_unit_lift ℂ k S hs (Fin k) (Iso.refl _) u

end HodgeLean.Foundations.Program.G32Native

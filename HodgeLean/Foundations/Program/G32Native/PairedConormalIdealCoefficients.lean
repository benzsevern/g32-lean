import HodgeLean.Foundations.Program.G32Native.PairedConormalIdealTransitions

/-! # Regular coefficients of actual ideal-module maps -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles

/-- The regular coefficient is the image of the specified actual ideal section. -/
def conormalIdealMapCoefficient {X : Scheme} (I : X.IdealSheafData)
    (φ : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.affineOpens) (a : Γ(X, U.1)) (ha : a ∈ I.ideal U) : Γ(X, U.1) :=
  φ.app U.1 (idealSection I U a ha)

/-- Original module maps retain the same transition factor as the original ideal equations. -/
theorem conormalIdealMapCoefficient_transition {X : Scheme} (I : X.IdealSheafData)
    (φ : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U V W : X.affineOpens) (hWU : W ≤ U) (hWV : W ≤ V)
    (a : Γ(X, U.1)) (ha : a ∈ I.ideal U)
    (c : Γ(X, V.1)) (hc : c ∈ I.ideal V) (r : Γ(X, W.1))
    (h : X.presheaf.map (homOfLE (show W.1 ≤ U.1 from hWU)).op a =
      r * X.presheaf.map (homOfLE (show W.1 ≤ V.1 from hWV)).op c) :
    X.presheaf.map (homOfLE (show W.1 ≤ U.1 from hWU)).op
        (conormalIdealMapCoefficient I φ U a ha) =
      r * X.presheaf.map (homOfLE (show W.1 ≤ V.1 from hWV)).op
        (conormalIdealMapCoefficient I φ V c hc) := by
  have hu := PresheafOfModules.naturality_apply φ.val
    (homOfLE (show W.1 ≤ U.1 from hWU)).op (idealSection I U a ha)
  have hv := PresheafOfModules.naturality_apply φ.val
    (homOfLE (show W.1 ≤ V.1 from hWV)).op (idealSection I V c hc)
  change φ.app W.1 ((idealModule I).presheaf.map
    (homOfLE (show W.1 ≤ U.1 from hWU)).op (idealSection I U a ha)) =
      X.presheaf.map (homOfLE (show W.1 ≤ U.1 from hWU)).op
        (conormalIdealMapCoefficient I φ U a ha) at hu
  change φ.app W.1 ((idealModule I).presheaf.map
    (homOfLE (show W.1 ≤ V.1 from hWV)).op (idealSection I V c hc)) =
      X.presheaf.map (homOfLE (show W.1 ≤ V.1 from hWV)).op
        (conormalIdealMapCoefficient I φ V c hc) at hv
  rw [← hu, conormal_ideal_generator_transition I U V W hWU hWV a ha c hc r h,
    Scheme.Modules.Hom.app_smul, hv]
  rfl

end HodgeLean.Foundations.Program.G32Native

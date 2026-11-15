import HodgeLean.Foundations.Curves.Picard.LineBundles.CartierFrames

/-! # Transition equations for sections of the actual kernel ideal -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles

/-- An equation between the original local ideal generators holds for their actual ideal sections. -/
theorem conormal_ideal_generator_transition {X : Scheme} (I : X.IdealSheafData)
    (U V W : X.affineOpens) (hWU : W ≤ U) (hWV : W ≤ V)
    (a : Γ(X, U.1)) (ha : a ∈ I.ideal U)
    (c : Γ(X, V.1)) (hc : c ∈ I.ideal V) (r : Γ(X, W.1))
    (h : X.presheaf.map (homOfLE (show W.1 ≤ U.1 from hWU)).op a =
      r * X.presheaf.map (homOfLE (show W.1 ≤ V.1 from hWV)).op c) :
    (idealModule I).presheaf.map (homOfLE (show W.1 ≤ U.1 from hWU)).op (idealSection I U a ha) =
      r • (idealModule I).presheaf.map (homOfLE (show W.1 ≤ V.1 from hWV)).op (idealSection I V c hc) := by
  apply (idealAffineSectionsEquiv I W).injective
  apply Subtype.ext
  rw [idealAffineSectionsEquiv_restrict I U W hWU, map_smul,
    idealSection_coordinate, Submodule.coe_smul_of_tower,
    idealAffineSectionsEquiv_restrict I V W hWV, idealSection_coordinate]
  exact h

end HodgeLean.Foundations.Program.G32Native

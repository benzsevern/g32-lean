import HodgeLean.Foundations.Program.SchoenTowerFoundC2Proofs

/-! # C2: retained-field pullback
Implication from an actual isomorphism of an integral scheme.
This first piece retains the contravariant generic square.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The deck isomorphism induces a unique pullback isomorphism on the retained field.
Source: EGA I, Chapter I, 2.4, functoriality of local rings; Mathlib,
`Scheme.SpecMap_stalkMap_fromSpecStalk`. -/
theorem s2t_functionField_deck (W : Scheme.{0}) [IsIntegral W]
    (d : W ≅ W) :
    ∃! e : W.functionField ≅ W.functionField,
      Spec.map e.hom ≫ W.fromSpecStalk (genericPoint W) =
        W.fromSpecStalk (genericPoint W) ≫ d.hom :=
  s2t_functionField_deck_aux W d

example := @s2t_functionField_deck

end HodgeLean.Foundations.Program

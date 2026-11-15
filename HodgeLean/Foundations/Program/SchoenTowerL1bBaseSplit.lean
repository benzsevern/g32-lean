import HodgeLean.Foundations.Program.SchoenTowerL1bBaseSplitProofs
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-! Interfaces for the base-coordinate construction. HC no distance; AV milestone no distance. -/

/-- A common affine neighborhood carries exact generators for both original selected branch ideals.
Source: Schoen (1988), Lemma 2.2, pp. 13–14; Hartshorne, Algebraic Geometry, II.6 and II.7.14. -/
alias s2v_l1b_base_common_chart := s2v_l1b_base_common_chart_aux

example : @s2v_l1b_base_common_chart = @s2v_l1b_base_common_chart_aux := rfl

/-- The simultaneous generators extend after affine refinement to etale coordinates.
Source: Schoen (1988), Lemma 2.2, pp. 13–14; Hartshorne, Algebraic Geometry, II.6 and II.7.14. -/
alias s2v_l1b_base_etale_extension := s2v_l1b_base_etale_extension_aux

example : @s2v_l1b_base_etale_extension = @s2v_l1b_base_etale_extension_aux := rfl

/-- Transport simultaneous etale branch coordinates through the retained earlier blowups and reduced transforms.
Source: Schoen (1988), Lemma 2.2, pp. 13–14; Hartshorne, Algebraic Geometry, II.6 and II.7.14. -/
alias s2v_l1b_base_tower_transport := s2v_l1b_base_tower_transport_aux

example : @s2v_l1b_base_tower_transport = @s2v_l1b_base_tower_transport_aux := rfl

end HodgeLean.Foundations.Program

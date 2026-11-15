import HodgeLean.Foundations.Program.SchoenTowerFinitePushforward
import HodgeLean.Foundations.Program.SchoenTowerActualSingularComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

theorem s2v_sheafPushforward_additive {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).Additive :=
  Functor.additive_of_preserves_binary_products _

theorem s2v_preimage_pushforward_preservesFiniteColimits {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B) :
    PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{0}
      (s2c_points.map (s2b_toExceptional β j))) := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} (s2c_points.map (s2b_toExceptional β j))
  letI : P.Additive := s2v_sheafPushforward_additive _
  apply ((Functor.preservesFiniteColimits_tfae P).out 1 4).mp
  intro S hS
  have h := s2v_preimage_pushforward_shortExact β j hS
  exact ⟨h.exact, h.epi_g⟩

attribute [local instance] s2v_sheafPushforward_additive

theorem s2v_preimage_pushedResolution_quasiIso {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) :
    QuasiIso (((TopCat.Sheaf.pushforward AddCommGrpCat.{0}
      (s2c_points.map (s2b_toExceptional β j))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (constantsToSingularCochainComplexInt (s2b_preimage β j) ℂ)) := by
  letI := s2v_preimage_pushforward_preservesFiniteColimits β j
  letI := s2v_constantsToSingularInt_quasiIso_of_contractible_basis (s2b_preimage β j) hX ℂ
  infer_instance

theorem s2v_preimage_pushedResolution_isFlasque {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) (j : E ⟶ B) (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((TopCat.Sheaf.pushforward AddCommGrpCat.{0}
      (s2c_points.map (s2b_toExceptional β j))).obj
        ((singularCochainSheafComplexInt (s2b_preimage β j) ℂ).X n)) := by
  letI : T2Space (ComplexPoint (s2b_preimage β j)) := s2v_pullback_points_t2 β j
  letI : ∀ U : Opens (ComplexPoint (s2b_preimage β j)), ParacompactSpace U :=
    s2v_projective_preimage_openParacompactSpace β j
  letI := spec_singularCochainSheafComplexInt_isFlasque_aux ℂ (s2b_preimage β j) n
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque _ _

end HodgeLean.Foundations.Program

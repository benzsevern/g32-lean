import HodgeLean.Foundations.Program.SchoenTowerProjectiveParacompact
import HodgeLean.Foundations.Program.SchoenTowerSingularComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

theorem s2v_projective_preimage_singularConstant_equiv
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) :
    ∃ c : AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint (s2b_preimage β j))) n ≃+
        Sheaf.H ((TopCat.Sheaf.constantFunctor
          (TopCat.of (ComplexPoint (s2b_preimage β j)))).obj (AddCommGrpCat.of ℂ)) n,
      ∀ (z : ℂ) v, c (z • v) =
        Sheaf.H.map (fieldScalarSheaf ℂ (s2b_preimage β j) z) n (c v) := by
  letI : T2Space (ComplexPoint (s2b_preimage β j)) := s2v_pullback_points_t2 β j
  letI : ∀ U : Opens (ComplexPoint (s2b_preimage β j)), ParacompactSpace U :=
    s2v_projective_preimage_openParacompactSpace β j
  exact s2v_singularConstant_equiv_with_coefficients (s2b_preimage β j) hX n

end HodgeLean.Foundations.Program

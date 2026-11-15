import HodgeLean.Foundations.Program.SchoenTowerActualSingularComparison
import HodgeLean.Foundations.Program.SchoenTowerFiniteDerivedComparison
import HodgeLean.Foundations.Program.SchoenTowerFinitePointFibres
import HodgeLean.Foundations.Program.SchoenTowerConstantCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

theorem s2v_actualFiniteCover_comparison_of_contractible_basis
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) : Nonempty (AlgebraicTopology.Singular.Cohomology ℂ
      (s2c_points.obj (s2b_preimage β j)) n ≃+
        Sheaf.H (s2c_coverSheaf (s2c_points.map (s2b_toExceptional β j))) n) := by
  let F := s2c_points.obj (s2b_preimage β j)
  let f := s2c_points.map (s2b_toExceptional β j)
  let C := (TopCat.Sheaf.constantFunctor F).obj (AddCommGrpCat.of ℂ)
  let P := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj C
  letI : CompactSpace F := s2v_pullback_points_compact β j
  letI : T2Space F := s2v_pullback_points_t2 β j
  have hfin : ∀ y, Set.Finite {x : F | f x = y} := fun y =>
    Set.finite_coe_iff.mp (s2v_preimage_point_fibre_finite β j y)
  obtain ⟨a, -⟩ := s2v_projective_preimage_singularConstant_equiv β j hX n
  let b := s2v_proper_finiteFibres_cohomologyEquiv f
    (s2v_projective_preimage_projection_proper β j) hfin C n
  let i := s2v_coverSheaf_pushforwardConstantIso f
  let c : Sheaf.H P n ≃+ Sheaf.H (s2c_coverSheaf f) n := {
    toFun := Sheaf.H.map i.inv n
    invFun := Sheaf.H.map i.hom n
    left_inv := by
      intro v
      rw [← Sheaf.H.map_comp_apply, i.inv_hom_id, Sheaf.H.map_id_apply]
    right_inv := by
      intro v
      rw [← Sheaf.H.map_comp_apply, i.hom_inv_id, Sheaf.H.map_id_apply]
    map_add' := by intro v w; exact map_add (Sheaf.H.map i.inv n) v w }
  exact ⟨a.trans (b.trans c)⟩

end HodgeLean.Foundations.Program

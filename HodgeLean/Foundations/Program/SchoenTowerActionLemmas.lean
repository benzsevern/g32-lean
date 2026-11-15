import HodgeLean.Foundations.Program.SchoenTowerFibreDefs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2v_coveringFibreDeck_projection {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K)
    (d : W ⟶ W) (hd : d ≫ β = β) (k : ComplexPoint K) :
    s2c_coveringFibreDeck β j p d hd k ≫ s2c_coveringFibreProjection β j p k =
      s2c_coveringFibreProjection β j p k := by
  apply pullback.hom_ext
  · simp only [Category.assoc, s2c_coveringFibreProjection, pullback.lift_fst,
      s2c_coveringFibreDeck, pullback.lift_fst_assoc,
      s2b_toExceptional, s2b_preimageDeck, pullback.lift_snd]
  · simp only [Category.assoc, s2c_coveringFibreProjection, pullback.lift_snd,
      s2c_coveringFibreDeck, pullback.lift_snd]

theorem s2v_preimageDeck_over_exceptional {W B E : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β) :
    s2c_points.map (s2b_preimageDeck β j d hd) ≫
      s2c_points.map (s2b_toExceptional β j) =
      s2c_points.map (s2b_toExceptional β j) := by
  rw [← s2c_points.map_comp]
  exact congrArg s2c_points.map (show s2b_preimageDeck β j d hd ≫
    s2b_toExceptional β j = s2b_toExceptional β j from pullback.lift_snd _ _ _)

end HodgeLean.Foundations.Program

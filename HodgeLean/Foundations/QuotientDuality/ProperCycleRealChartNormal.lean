import HodgeLean.Foundations.QuotientDuality.ProperCycleRealVectorShift

/-! # Normal local homology in actual finite real vector charts -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Excision and the actual finite real-vector shift identify ambient and normal local homology.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
def properCycle_real_chart_normal_homology_iso
    (X : TopCat.{0}) [T1Space X] (W : Opens X)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] (e : W ≃ₜ (E × Y)) (w : W) (j : ℕ) :
    orientationGroup X (j + Module.finrank ℝ E) (w : X) ≅ orientationGroup Y j (e w).2 := by
  let t : (E × Y) ≃ₜ (E × Y) :=
    { toFun := fun z => (z.1 - (e w).1, z.2)
      invFun := fun z => (z.1 + (e w).1, z.2)
      left_inv := by intro z; apply Prod.ext <;> simp
      right_inv := by intro z; apply Prod.ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have ht : t (e w) = (0, (e w).2) := Prod.ext (sub_self _) rfl
  let H := properCycle_local_homology_homeomorph_iso
    (X := TopCat.of (E × Y)) (Y := TopCat.of (E × Y)) t (e w) (j + Module.finrank ℝ E)
  rw [ht] at H
  exact (properCycle_open_local_homology_iso X W w (j + Module.finrank ℝ E)).symm ≪≫
    properCycle_local_homology_homeomorph_iso
      (X := TopCat.of W) (Y := TopCat.of (E × Y)) e w (j + Module.finrank ℝ E) ≪≫ H ≪≫
    properCycle_vector_product_local_homology_iso E Y (e w).2 j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ambient local vanishing gives shifted normal local vanishing in an actual real-vector product chart.
Source: Bredon, Sheaf Theory, second edition, V.9, normal product models.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_chart_normal_homology_subsingleton
    (X : TopCat.{0}) [T1Space X] (W : Opens X)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] (e : W ≃ₜ (E × Y)) (w : W) (j : ℕ)
    (hvan : Subsingleton (orientationGroup X (j + Module.finrank ℝ E) (w : X))) :
    Subsingleton (orientationGroup Y j (e w).2) := by
  let H := properCycle_real_chart_normal_homology_iso X W E Y e w j
  exact @Function.Injective.subsingleton _ _ H.toLinearEquiv.symm
    H.toLinearEquiv.symm.injective hvan

end HodgeLean.Foundations.QuotientDuality

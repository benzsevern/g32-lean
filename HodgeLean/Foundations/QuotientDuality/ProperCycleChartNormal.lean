import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexShift

/-! # Normal local homology obtained from the ambient product chart -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Excision, tangential recentering and the actual product shift identify ambient and normal local homology.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
def properCycle_chart_normal_homology_iso
    (X : TopCat.{0}) [T1Space X] (W : Opens X) (r : ℕ)
    (Y : TopCat.{0}) [T1Space Y] (e : W ≃ₜ ((Fin r → ℂ) × Y))
    (w : W) (j : ℕ) :
    orientationGroup X (j + 2 * r) (w : X) ≅ orientationGroup Y j (e w).2 := by
  let t : ((Fin r → ℂ) × Y) ≃ₜ ((Fin r → ℂ) × Y) :=
    { toFun := fun z => (z.1 - (e w).1, z.2)
      invFun := fun z => (z.1 + (e w).1, z.2)
      left_inv := by intro z; apply Prod.ext <;> simp
      right_inv := by intro z; apply Prod.ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have ht : t (e w) = (0, (e w).2) := Prod.ext (sub_self _) rfl
  let E := properCycle_local_homology_homeomorph_iso
    (X := TopCat.of ((Fin r → ℂ) × Y)) (Y := TopCat.of ((Fin r → ℂ) × Y))
    t (e w) (j + 2 * r)
  rw [ht] at E
  exact (properCycle_open_local_homology_iso X W w (j + 2 * r)).symm ≪≫
    properCycle_local_homology_homeomorph_iso
      (X := TopCat.of W) (Y := TopCat.of ((Fin r → ℂ) × Y)) e w (j + 2 * r) ≪≫ E ≪≫
    properCycle_complex_pi_local_homology_iso r Y (e w).2 j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ambient local homology vanishing transfers to the shifted normal degree in an actual product chart.
Source: Bredon, Sheaf Theory, second edition, V.9, normal product models.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_normal_homology_subsingleton
    (X : TopCat.{0}) [T1Space X] (W : Opens X) (r : ℕ)
    (Y : TopCat.{0}) [T1Space Y] (e : W ≃ₜ ((Fin r → ℂ) × Y))
    (w : W) (j : ℕ)
    (hvan : Subsingleton (orientationGroup X (j + 2 * r) (w : X))) :
    Subsingleton (orientationGroup Y j (e w).2) := by
  let E := properCycle_chart_normal_homology_iso X W r Y e w j
  exact @Function.Injective.subsingleton _ _ E.toLinearEquiv.symm
    E.toLinearEquiv.symm.injective hvan

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified ambient local orientation yields a normal homology generator through the actual chart shift.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_normal_homology_generator
    (X : TopCat.{0}) [T1Space X] (W : Opens X) (r : ℕ)
    (Y : TopCat.{0}) [T1Space Y] (e : W ≃ₜ ((Fin r → ℂ) × Y))
    (w : W) (j : ℕ) (c : Homology ℚ X (j + 2 * r))
    (hlocal : Function.Bijective (orientationLine X (j + 2 * r) c (w : X))) :
    Function.Bijective (LinearMap.toSpanSingleton ℚ (orientationGroup Y j (e w).2)
      ((properCycle_chart_normal_homology_iso X W r Y e w j).hom
        (localOrientation X (j + 2 * r) c (w : X)))) := by
  let E := properCycle_chart_normal_homology_iso X W r Y e w j
  have he : LinearMap.toSpanSingleton ℚ (orientationGroup Y j (e w).2)
      (E.hom (localOrientation X (j + 2 * r) c (w : X))) =
      E.hom.hom.comp (orientationLine X (j + 2 * r) c (w : X)) := by
    apply LinearMap.ext
    intro q
    change q • E.hom _ = E.hom (q • _)
    exact (map_smul E.hom.hom q _).symm
  rw [he]
  exact E.toLinearEquiv.bijective.comp hlocal

end HodgeLean.Foundations.QuotientDuality

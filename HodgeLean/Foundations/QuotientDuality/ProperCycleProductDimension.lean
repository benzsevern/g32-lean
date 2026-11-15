import HodgeLean.Foundations.QuotientDuality.ProperCycleProductLowDegree
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealChartNormal

/-! # Dimension detection from actual local homology in product charts -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Local homology below the real tangential dimension of an actual finite product vanishes.
Source: Hatcher, Algebraic Topology, section 2.2, relative sequences and local product calculations.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_pi_local_subsingleton_of_lt
    (r : ℕ) (Y : TopCat.{0}) [T1Space Y] (y : Y) (n : ℕ) (hn : n < r) :
    Subsingleton (orientationGroup (TopCat.of ((Fin r → ℝ) × Y)) n (0, y)) := by
  induction r generalizing n with
  | zero => omega
  | succ r ih =>
      let e : ((Fin (r + 1) → ℝ) × Y) ≃ₜ (ℝ × ((Fin r → ℝ) × Y)) :=
        ((properCycle_real_fin_succ_homeomorph r).prodCongr (Homeomorph.refl Y)).trans
          (Homeomorph.prodAssoc ℝ (Fin r → ℝ) Y)
      have he : e (0, y) = (0, (0, y)) := rfl
      let H := properCycle_local_homology_homeomorph_iso
        (X := TopCat.of ((Fin (r + 1) → ℝ) × Y))
        (Y := TopCat.of (ℝ × ((Fin r → ℝ) × Y))) e (0, y) n
      rw [he] at H
      cases n with
      | zero =>
          exact @Function.Injective.subsingleton _ _ H.toLinearEquiv H.toLinearEquiv.injective
            (properCycle_real_product_local_zero (TopCat.of ((Fin r → ℝ) × Y)) (0, y))
      | succ n =>
          let H' := H ≪≫ properCycle_real_product_local_homology_iso
            (TopCat.of ((Fin r → ℝ) × Y)) (0, y) n
          exact @Function.Injective.subsingleton _ _ H'.toLinearEquiv H'.toLinearEquiv.injective
            (ih n (by omega))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Local homology vanishes below the dimension of an actual finite real normed factor.
Source: Hatcher, Algebraic Topology, section 2.2, local product calculations.
HC no distance; AV milestone no distance. -/
lemma properCycle_vector_local_subsingleton_of_lt
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] (y : Y) (n : ℕ) (hn : n < Module.finrank ℝ E) :
    Subsingleton (orientationGroup (TopCat.of (E × Y)) n (0, y)) := by
  let e := properCycle_vector_product_coordinates E Y
  have he : e (0, y) = (0, y) := by
    apply Prod.ext
    · exact (ContinuousLinearEquiv.ofFinrankEq
        (by simp only [Module.finrank_pi, Fintype.card_fin]) :
          E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)).map_zero
    · rfl
  let H := properCycle_local_homology_homeomorph_iso
    (X := TopCat.of (E × Y)) (Y := TopCat.of ((Fin (Module.finrank ℝ E) → ℝ) × Y)) e (0, y) n
  rw [he] at H
  exact @Function.Injective.subsingleton _ _ H.toLinearEquiv H.toLinearEquiv.injective
    (properCycle_real_pi_local_subsingleton_of_lt (Module.finrank ℝ E) Y y n hn)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A nonzero actual local class bounds the dimension of the tangential factor of an actual product chart.
Source: Hatcher, Algebraic Topology, section 2.2, local homology and invariance of dimension.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_dimension_le_of_local_ne_zero
    (X : TopCat.{0}) [T1Space X] (W : Opens X)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) (e : W ≃ₜ (E × Y)) (w : W) (n : ℕ)
    (c : orientationGroup X n (w : X)) (hc : c ≠ 0) :
    Module.finrank ℝ E ≤ n := by
  letI : T1Space (E × Y) := e.t1Space
  letI : T1Space Y := t1Space_of_injective_of_continuous
    (f := fun y : Y => ((0 : E), y))
    (fun a b h => congrArg Prod.snd h) (continuous_const.prodMk continuous_id)
  let t : (E × Y) ≃ₜ (E × Y) :=
    { toFun := fun z => (z.1 - (e w).1, z.2)
      invFun := fun z => (z.1 + (e w).1, z.2)
      left_inv := by intro z; apply Prod.ext <;> simp
      right_inv := by intro z; apply Prod.ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have ht : t (e w) = (0, (e w).2) := Prod.ext (sub_self _) rfl
  let Ht := properCycle_local_homology_homeomorph_iso
    (X := TopCat.of (E × Y)) (Y := TopCat.of (E × Y)) t (e w) n
  rw [ht] at Ht
  let H := (properCycle_open_local_homology_iso X W w n).symm ≪≫
    properCycle_local_homology_homeomorph_iso
      (X := TopCat.of W) (Y := TopCat.of (E × Y)) e w n ≪≫ Ht
  by_contra h
  have hsub := properCycle_vector_local_subsingleton_of_lt E Y (e w).2 n (by omega)
  have hsource : Subsingleton (orientationGroup X n (w : X)) :=
    @Function.Injective.subsingleton _ _ H.toLinearEquiv H.toLinearEquiv.injective hsub
  exact hc (hsource.elim _ _)

end HodgeLean.Foundations.QuotientDuality

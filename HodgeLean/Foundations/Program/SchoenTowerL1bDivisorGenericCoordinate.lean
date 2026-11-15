import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductFunction
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorGenericStalk

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A coordinate projecting to the generic point makes every nonzero curve function a stalk unit. -/
theorem s2v_l1b_divisor_generic_coordinate_unit
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) (hx : f x = genericPoint Y)
    (v : Y.functionField) (hv : v ≠ 0) :
    ∃ a : X.presheaf.stalk x, IsUnit a ∧
      algebraMap _ X.functionField a = s2v_l1b_functionFieldPullback f v := by
  have hfield : IsField (Y.presheaf.stalk (f x)) := by
    rw [hx]
    exact Field.toIsField Y.functionField
  have hsurj : Function.Surjective (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) :=
    IsFractionRing.surjective_iff_isField.mpr hfield
  let e : Y.presheaf.stalk (f x) ≃+* Y.functionField :=
    RingEquiv.ofBijective (algebraMap _ _) ⟨IsFractionRing.injective _ _, hsurj⟩
  let a := (f.stalkMap x).hom (e.symm v)
  refine ⟨a, ((isUnit_iff_ne_zero.mpr hv).map e.symm.toRingHom).map (f.stalkMap x).hom, ?_⟩
  have H := s2v_l1b_divisor_generic_stalk f x (e.symm v)
  change s2v_l1b_functionFieldPullback f (e (e.symm v)) = algebraMap _ X.functionField a at H
  rw [e.apply_symm_apply] at H
  exact H.symm

/-- If all coordinates are generic, the entire coordinate product is represented by a stalk unit. -/
theorem s2v_l1b_divisor_generic_product_unit
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (n : ℕ) [IsIntegral (g3_power Y n).left]
    (x : (g3_power Y n).left)
    (hx : ∀ i, (g3_proj Y n i).left x = genericPoint Y.left)
    (v : Y.left.functionField) (hv : v ≠ 0) :
    ∃ a : (g3_power Y n).left.presheaf.stalk x, IsUnit a ∧
      algebraMap _ (g3_power Y n).left.functionField a =
        s2v_l1b_divisor_product_function Y n v := by
  letI : ∀ i : Fin n, IsDominant (g3_proj Y n i).left :=
    s2v_l1b_divisor_projection_dominant Y n
  choose a haunit haeq using fun i =>
    s2v_l1b_divisor_generic_coordinate_unit (g3_proj Y n i).left x (hx i) v hv
  refine ⟨∏ i, a i, IsUnit.prod_univ_iff.mpr haunit, ?_⟩
  rw [map_prod]
  simp_rw [haeq]
  rfl

/-- Generic coordinates away from one specified index contribute a single stalk unit to the coordinate product. -/
theorem s2v_l1b_divisor_product_one_coordinate_unit
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (n : ℕ) [IsIntegral (g3_power Y n).left]
    (x : (g3_power Y n).left) (i : Fin n)
    (hx : ∀ j, j ≠ i → (g3_proj Y n j).left x = genericPoint Y.left)
    (v : Y.left.functionField) (hv : v ≠ 0) :
    letI := s2v_l1b_divisor_projection_dominant Y n i
    ∃ u : (g3_power Y n).left.presheaf.stalk x, IsUnit u ∧
      s2v_l1b_divisor_product_function Y n v =
        s2v_l1b_functionFieldPullback (g3_proj Y n i).left v *
          algebraMap _ (g3_power Y n).left.functionField u := by
  classical
  letI : ∀ j : Fin n, IsDominant (g3_proj Y n j).left :=
    s2v_l1b_divisor_projection_dominant Y n
  have hex (j : Fin n) : ∃ a : (g3_power Y n).left.presheaf.stalk x,
      IsUnit a ∧ (j ≠ i → algebraMap _ (g3_power Y n).left.functionField a =
        s2v_l1b_functionFieldPullback (g3_proj Y n j).left v) := by
    by_cases hji : j = i
    · exact ⟨1, isUnit_one, fun h => False.elim (h hji)⟩
    · obtain ⟨a, ha, hae⟩ := s2v_l1b_divisor_generic_coordinate_unit
        (g3_proj Y n j).left x (hx j hji) v hv
      exact ⟨a, ha, fun _ => hae⟩
  choose a ha hae using hex
  refine ⟨∏ j ∈ Finset.univ.erase i, a j, ?_, ?_⟩
  · exact IsUnit.prod_iff.mpr (fun j _ => ha j)
  · rw [map_prod]
    change (∏ j, s2v_l1b_functionFieldPullback (g3_proj Y n j).left v) = _
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact (hae j (Finset.mem_erase.mp hj).1).symm

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.CompensationCubicGroupProofs
import HodgeLean.Foundations.Curves.CubicGrpObjProofs

set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.CompensationCubic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.Foundations.Curves (complexPoint_hom_ext_aux locallyOfFiniteType_tensor_hom)

theorem isReduced_cubic_tensor_aux :
    IsReduced (E ⊗ E).left ∧ IsReduced ((E ⊗ E) ⊗ E).left ∧ IsReduced (E ⊗ (E ⊗ E)).left := by
  have : IsIntegral (E ⊗ E).left :=
    isIntegral_pullback_of_isAlgClosed ℂ E.left E.left E.hom E.hom
  have := locallyOfFiniteType_tensor_hom E E
  have : IsIntegral ((E ⊗ E) ⊗ E).left :=
    isIntegral_pullback_of_isAlgClosed ℂ (E ⊗ E).left E.left (E ⊗ E).hom E.hom
  have : IsIntegral (E ⊗ (E ⊗ E)).left :=
    isIntegral_pullback_of_isAlgClosed ℂ E.left (E ⊗ E).left E.hom (E ⊗ E).hom
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem exists_grpObj_aux (e : ComplexPoint E ≃ W.toAffine.Point) (hO : e (Over.homMk infinity infinity_over : ComplexPoint E) = 0)
    (m : E ⊗ E ⟶ E) (hm : ∀ P Q : ComplexPoint E, lift P Q ≫ m = e.symm (e P + e Q))
    (i : E ⟶ E) (hi : ∀ P : ComplexPoint E, P ≫ i = e.symm (-e P)) :
    ∃ G : GrpObj E, G.one = Over.homMk infinity infinity_over ∧ G.mul = m ∧ G.inv = i := by
  have hred := isReduced_cubic_tensor_aux
  have := hred.2.1
  have := locallyOfFiniteType_tensor_hom E E
  have := locallyOfFiniteType_tensor_hom (E ⊗ E) E
  have hu : ∀ P : ComplexPoint E, P ≫ toUnit E = 𝟙 _ := fun P ↦ toUnit_unique _ _
  refine ⟨{ one := Over.homMk infinity infinity_over, mul := m, inv := i
            one_mul := ?_, mul_one := ?_, mul_assoc := ?_, left_inv := ?_, right_inv := ?_ },
    rfl, rfl, rfl⟩
  · rw [← cancel_epi (λ_ E).inv, Iso.inv_hom_id]
    refine complexPoint_hom_ext_aux fun P ↦ ?_
    have : P ≫ (λ_ E).inv ≫ Over.homMk infinity infinity_over ▷ E =
        lift (Over.homMk infinity infinity_over) P := by
      ext <;> simp [reassoc_of% hu]
    rw [reassoc_of% this, hm, hO, zero_add, Equiv.symm_apply_apply, Category.comp_id]
  · rw [← cancel_epi (ρ_ E).inv, Iso.inv_hom_id]
    refine complexPoint_hom_ext_aux fun P ↦ ?_
    have : P ≫ (ρ_ E).inv ≫ E ◁ Over.homMk infinity infinity_over =
        lift P (Over.homMk infinity infinity_over) := by
      ext <;> simp [reassoc_of% hu]
    rw [reassoc_of% this, hm, hO, add_zero, Equiv.symm_apply_apply, Category.comp_id]
  · refine complexPoint_hom_ext_aux fun P ↦ ?_
    have hP : P = lift (lift (P ≫ fst _ _ ≫ fst _ _) (P ≫ fst _ _ ≫ snd _ _)) (P ≫ snd _ _) := by
      ext <;> simp
    rw [hP]
    simp [hm, add_assoc]
  · refine complexPoint_hom_ext_aux fun P ↦ ?_
    rw [comp_lift_assoc, Category.comp_id, hm, hi, Equiv.apply_symm_apply, reassoc_of% hu]
    simp [Equiv.symm_apply_eq, hO]
  · refine complexPoint_hom_ext_aux fun P ↦ ?_
    rw [comp_lift_assoc, Category.comp_id, hm, hi, Equiv.apply_symm_apply, reassoc_of% hu]
    simp [Equiv.symm_apply_eq, hO]


end HodgeLean.Foundations.Program.CompensationCubic

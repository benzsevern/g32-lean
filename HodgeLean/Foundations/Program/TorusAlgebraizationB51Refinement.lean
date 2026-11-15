import HodgeLean.Foundations.Program.TorusAlgebraizationDefs

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b5_refinement_add_defect_even (Λ : Type*) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (Q : LinearMap.BilinForm ℤ Λ)
    (hQ : ∀ x, Q x x = 0) (l m : Λ) :
    ∃ k : ℤ, b5_refinement Λ Q (l + m) - b5_refinement Λ Q l -
      b5_refinement Λ Q m - Q l m = 2 * k := by
  classical
  let b := Module.finBasis ℤ Λ
  let B : LinearMap.BilinForm ℤ Λ := b.constr ℤ fun i ↦
    b.constr ℤ fun j ↦ if i < j then Q (b i) (b j) else 0
  have hB (x : Λ) : b5_refinement Λ Q x = B x x := by
    symm
    calc
      B x x = B (∑ i, (b.repr x i) • b i) (∑ j, (b.repr x j) • b j) := by
        rw [b.sum_repr x]
      _ = b5_refinement Λ Q x := by
        simp [b5_refinement, B, b, map_sum, LinearMap.sum_apply, map_zsmul, zsmul_eq_mul,
          Finset.mul_sum, mul_ite, mul_assoc]
  have hskew (x y : Λ) : Q x y = B x y - B y x := by
    have hxy : Q = B - B.flip := by
      refine LinearMap.ext_basis b b fun i j ↦ ?_
      simp only [LinearMap.sub_apply, LinearMap.BilinForm.flip_apply, B,
        Module.Basis.constr_basis]
      by_cases hij : i < j
      · simp only [hij, if_true]
        have hji : ¬ j < i := not_lt_of_ge (le_of_lt hij)
        simp only [hji, if_false, sub_zero]
      · by_cases heq : i = j
        · subst j
          simp only [lt_self_iff_false, if_false, sub_zero, hQ]
        · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm heq)
          simp only [hij, if_false, hji, if_true, zero_sub]
          have ha := hQ (b i + b j)
          simp only [map_add, LinearMap.add_apply, hQ, zero_add, add_zero] at ha
          exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans ha)
    simpa [hxy]
  refine ⟨B m l, ?_⟩
  rw [hB, hB, hB, hskew]
  simp only [map_add, LinearMap.add_apply]
  ring

end HodgeLean.Foundations.Program

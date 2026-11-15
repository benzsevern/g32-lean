import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartBaseChange

/-! # Actual tensor chart coordinates and polynomial residue classes -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped TensorProduct BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual normalized polynomial class of a homogeneous coordinate ratio.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_baseChangedChartAlgEquiv_coordinate (R : Type*) [CommRing R]
    {n : ℕ} (i j : Fin (n + 1)) :
    s2e_baseChangedChartAlgEquiv R i ((1 : R) ⊗ₜ[ℤ] chartCoordinate i j) =
      Ideal.Quotient.mk (Ideal.span ({MvPolynomial.X i - 1} : Set (MvPolynomial (Fin (n + 1)) R)))
        (if j = i then 1 else MvPolynomial.X j) := by
  simp only [s2e_baseChangedChartAlgEquiv, AlgEquiv.trans_apply]
  simp [s2e_integralChartRingEquivInt, s2e_integralChartRingEquiv,
    s2e_integralChartAwayHom_coordinate, MvPolynomial.mapEquiv_apply]
  split_ifs <;> simp

/-- A normalized linear polynomial represents the actual linear combination of homogeneous chart ratios.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_baseChangedChartAlgEquiv_symm_linear (R : Type*) [CommRing R]
    {n : ℕ} (i : Fin (n + 1)) (a : Fin (n + 1) → R) :
    (s2e_baseChangedChartAlgEquiv R i).symm
      (Ideal.Quotient.mk (Ideal.span ({MvPolynomial.X i - 1} : Set (MvPolynomial (Fin (n + 1)) R)))
        (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j)) =
      ∑ j, algebraMap R _ (a j) * ((1 : R) ⊗ₜ[ℤ] chartCoordinate i j) := by
  classical
  let π := Ideal.Quotient.mk
    (Ideal.span ({MvPolynomial.X i - 1} : Set (MvPolynomial (Fin (n + 1)) R)))
  have hXi : π (MvPolynomial.X i) = 1 := by
    have hz : π (MvPolynomial.X i - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  apply (s2e_baseChangedChartAlgEquiv R i).injective
  rw [AlgEquiv.apply_symm_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul, map_mul, AlgEquiv.commutes, s2e_baseChangedChartAlgEquiv_coordinate]
  change π (MvPolynomial.C (a j)) * π (MvPolynomial.X j) =
    π (MvPolynomial.C (a j)) * π (if j = i then 1 else MvPolynomial.X j)
  by_cases h : j = i
  · subst j
    simp [hXi]
  · rw [if_neg h]

end HodgeLean.Foundations.Program

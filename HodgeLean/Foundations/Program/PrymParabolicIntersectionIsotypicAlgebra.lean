import HodgeLean.Foundations.Program.PrymParabolicIntersectionWeilAlgebra

noncomputable section
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem hga_cellOperator_skew_of_centre_invariant
    (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hC : ∀ x y, B (hg6_cellCentre x) (hg6_cellCentre y) = B x y)
    (a b : hg6_cellLattice) :
    B (hg6_cellOperator a) b = -B a (hg6_cellOperator b) := by
  have hpoly := hg6_saturation_polynomial (hg2_H1act ℤ b4b_root)
    hg6_H1act_mul_apply a.val a.property
  have hc : hg6_cellCentre = hg2_H1act ℤ b4b_root b63d_scalarElement :=
    hg6_centreOf_eq _
  rw [← hc] at hpoly
  have h := congrArg (fun z ↦ B z (hg6_cellCentre b.val)) hpoly
  simp only [map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply] at h
  rw [hC, hC] at h
  change B (a.val + 2 • hg6_cellCentre a.val) b.val =
    -B a.val (b.val + 2 • hg6_cellCentre b.val)
  simp only [two_nsmul, map_add, LinearMap.add_apply]
  omega

theorem hga_projectorCoeff_inv (g : b4b_Group) :
    b4b_projectorCoeff g⁻¹ = b4b_projectorCoeff g := by
  unfold b4b_projectorCoeff
  rw [inv_inv, b63l_toMatrix_entry_inv]
  simp only [Complex.conj_re]

theorem hga_deck_adjoint
    (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hB : ∀ g x y, B (hg2_H1act ℤ b4b_root g x) (hg2_H1act ℤ b4b_root g y) = B x y)
    (g : b4b_Group) (x y : hg2_H1 ℤ b4b_root) :
    B (hg2_H1act ℤ b4b_root g x) y = B x (hg2_H1act ℤ b4b_root g⁻¹ y) := by
  have h := hB g x (hg2_H1act ℤ b4b_root g⁻¹ y)
  rwa [hg6_H1act_mul_apply, mul_inv_cancel, hg2_H1act_one, LinearMap.id_apply] at h

set_option backward.isDefEq.respectTransparency false in
theorem hga_projector_selfAdjoint
    (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hB : ∀ g x y, B (hg2_H1act ℤ b4b_root g x) (hg2_H1act ℤ b4b_root g y) = B x y)
    (x y : hg2_H1 ℤ b4b_root) : B (hg2_projector x) y = B x (hg2_projector y) := by
  have hP (z : hg2_H1 ℤ b4b_root) : hg2_projector z =
      ∑ g, b4b_projectorCoeff g • hg2_H1act ℤ b4b_root g z := hg6_projOf_apply _ z
  rw [hP, hP]
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply]
  simp_rw [hga_deck_adjoint B hB]
  refine Fintype.sum_equiv (Equiv.inv b4b_Group) _ _ fun g ↦ ?_
  simp only [Equiv.inv_apply, hga_projectorCoeff_inv]

theorem hga_projector_on_lattice (a : hg6_cellLattice) :
    hg2_projector a = b4b_projectorDenominator • a.val := by
  obtain ⟨n, hn, y, hy⟩ := (hg6_mem_saturation_iff _ _).mp a.property
  apply sub_eq_zero.mp
  apply hg6_zsmul_eq_zero hn
  rw [zsmul_sub, ← map_zsmul, ← hy, hg2_projector_square, hy,
    smul_comm n b4b_projectorDenominator, sub_self]

set_option backward.isDefEq.respectTransparency false in
theorem hga_isotypic_coordinate_evaluation
    (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hB : ∀ g x y, B (hg2_H1act ℤ b4b_root g x) (hg2_H1act ℤ b4b_root g y) = B x y)
    (c : hg_eqCocycles hg4_sigmaK b4b_root) (a : hg6_cellLattice)
    (hdual : ∀ x : hg6_cellLattice,
      hg6_evalVec hg4_sigmaK b4b_root c x 0 = hga_cellWeil B a x)
    (z : hg2_H1 ℤ b4b_root) :
    hg6_evalVec hg4_sigmaK b4b_root c z 0 =
      -((B (hg6_cellOperator a) z : ℤ) : hp_K) +
        QuadraticAlgebra.omega * ((B a z : ℤ) : hp_K) := by
  have hD : (b4b_projectorDenominator : hp_K) ≠ 0 := by
    norm_num [b4b_projectorDenominator]
  apply mul_left_cancel₀ hD
  have he := congrFun (hg6_evalVec_projector c z) 0
  have he' : hg6_evalVec hg4_sigmaK b4b_root c (hg2_projector z) 0 =
      (b4b_projectorDenominator : hp_K) * hg6_evalVec hg4_sigmaK b4b_root c z 0 := by
    simpa only [Pi.smul_apply, Pi.single_eq_same, zsmul_eq_mul] using he
  rw [← he', hdual ⟨hg2_projector z, hg6_projector_mem_lattice z⟩]
  have hC : ∀ x y, B (hg6_cellCentre x) (hg6_cellCentre y) = B x y := by
    intro x y
    simpa only [hg6_cellCentre, hg6_centreOf_eq] using hB b63d_scalarElement x y
  have hJ := hga_cellOperator_skew_of_centre_invariant B hC a
    ⟨hg2_projector z, hg6_projector_mem_lattice z⟩
  have hJ' : B a (hg6_cellOperator ⟨hg2_projector z, hg6_projector_mem_lattice z⟩) =
      -B (hg6_cellOperator a) (hg2_projector z) := neg_eq_iff_eq_neg.mp hJ.symm
  rw [hga_cellWeil, hJ',
    ← hga_projector_selfAdjoint B hB (hg6_cellOperator a).val z,
    ← hga_projector_selfAdjoint B hB a.val z,
    hga_projector_on_lattice (hg6_cellOperator a), hga_projector_on_lattice a]
  simp only [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
  push_cast
  ring

theorem hga_cellOperator_bilinear
    (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hJ : ∀ x y : hg6_cellLattice,
      B (hg6_cellOperator x) y = -B x (hg6_cellOperator y)) (a b : hg6_cellLattice) :
    B (hg6_cellOperator a) (hg6_cellOperator b) = 3 * B a b := by
  rw [hJ, hg6_cellOperator_sq]
  change -(B a ((-3 : ℤ) • b.val)) = _
  rw [map_smul]
  simp [smul_eq_mul]

#print axioms hga_cellOperator_bilinear

#print axioms hga_isotypic_coordinate_evaluation

#print axioms hga_projector_on_lattice

#print axioms hga_projector_selfAdjoint

#print axioms hga_deck_adjoint

#print axioms hga_projectorCoeff_inv

#print axioms hga_cellOperator_skew_of_centre_invariant
end HodgeLean.Foundations.Program

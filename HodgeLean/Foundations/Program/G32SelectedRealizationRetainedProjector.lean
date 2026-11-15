import HodgeLean.Foundations.Program.G32SelectedRealizationLatticeProjector

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

theorem g32y_retained_lattice_projector {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    ∃ N : ℕ, 0 < N ∧ ∃ z : g32p_G → ℤ,
      let T := b4_groupEnd ℂ (C := b65z_fibre c D.C t) z
      (∀ x, T (T x) = (N : ℤ) • T x) ∧
        b63l_saturation T.toIntLinearMap.range = b63l_periodLattice (b65z_fibre c D.C t) := by
  let R : Representation ℤ g32p_G (g32x_L D t) := {
    toFun := fun h ↦ (b4_latticeAct ℂ h).toIntLinearMap
    map_one' := by
      change (b4_latticeAct ℂ (C := b65z_fibre c D.C t) 1).toIntLinearMap = 1
      rw [b4_latticeAct_one (D.hG t)]
      rfl
    map_mul' := by
      intro a b
      change (b4_latticeAct ℂ (C := b65z_fibre c D.C t) (a * b)).toIntLinearMap = _
      rw [b4_latticeAct_mul (D.hG t)]
      rfl }
  have hzlin (z : g32p_G → ℤ) :
      (b4_groupEnd ℂ (C := b65z_fibre c D.C t) z).toIntLinearMap = ∑ h, z h • R h := by
    apply LinearMap.ext
    intro x
    simp only [b4_groupEnd, AddMonoidHom.coe_toIntLinearMap,
      AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply,
      LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  obtain ⟨N, hN, z, hT, hS⟩ := g32y_integral_image_projector R b4b_projectorCoeff
  refine ⟨N, hN, z, ?_, ?_⟩
  · intro x
    change (b4_groupEnd ℂ (C := b65z_fibre c D.C t) z).toIntLinearMap
      ((b4_groupEnd ℂ z).toIntLinearMap x) =
        (N : ℤ) • (b4_groupEnd ℂ (C := b65z_fibre c D.C t) z).toIntLinearMap x
    rw [hzlin]
    exact hT x
  · change b63l_saturation (b4_groupEnd ℂ (C := b65z_fibre c D.C t) z).toIntLinearMap.range =
      b63l_saturation (b4_groupEnd ℂ (C := b65z_fibre c D.C t) b4b_projectorCoeff).toIntLinearMap.range
    rw [hzlin, hzlin]
    exact hS

theorem g32y_groupEnd_centre_commute {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (z : g32p_G → ℤ)
    (x : g32x_L D t) :
    b4_groupEnd ℂ z (b4_latticeAct ℂ b63d_scalarElement x) =
      b4_latticeAct ℂ b63d_scalarElement (b4_groupEnd ℂ z x) := by
  classical
  simp only [b4_groupEnd, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro h _
  apply congrArg (fun y ↦ (z h : ℤ) • y)
  calc
    b4_latticeAct ℂ h (b4_latticeAct ℂ b63d_scalarElement x) =
        b4_latticeAct ℂ (h * b63d_scalarElement) x := by
      rw [b4_latticeAct_mul (D.hG t)]
      rfl
    _ = b4_latticeAct ℂ (b63d_scalarElement * h) x := by
      rw [b63d_scalar_commutes b63d_scalarElement h b63d_scalarElement_matrix]
    _ = b4_latticeAct ℂ b63d_scalarElement (b4_latticeAct ℂ h x) := by
      rw [b4_latticeAct_mul (D.hG t)]
      rfl

theorem g32y_retained_projector_square {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (x : g32x_L D t) :
    b4_groupEnd ℂ b4b_projectorCoeff (b4_groupEnd ℂ b4b_projectorCoeff x) =
      b4b_projectorDenominator • b4_groupEnd ℂ b4b_projectorCoeff x := by
  classical
  have hcomp (g k : b4b_Group) (y : g32x_L D t) :
      b4_latticeAct ℂ g (b4_latticeAct ℂ k y) = b4_latticeAct ℂ (g * k) y := by
    rw [b4_latticeAct_mul (D.hG t)]
    rfl
  have hreindex (g : b4b_Group) :
      (∑ k : b4b_Group, (b4b_projectorCoeff g * b4b_projectorCoeff k) •
        b4_latticeAct ℂ (g * k) x) =
      ∑ h : b4b_Group, (b4b_projectorCoeff g * b4b_projectorCoeff (g⁻¹ * h)) •
        b4_latticeAct ℂ h x := by
    simpa only [inv_mul_cancel_left] using
      Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ (fun k ↦ by simp)
  simp only [b4_groupEnd, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply,
    map_sum, map_zsmul, Finset.smul_sum, smul_smul, hcomp]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, g, 2, k]
    rw [mul_comm (b4b_projectorCoeff k) (b4b_projectorCoeff g)]
  simp_rw [hreindex]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, b63l_projector_convolution]

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32SelectedRealizationMarked

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

theorem g32y_reference_centre_transport {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (x : b63l_parameterLattice c D.C D.hC (b6t_polydisc c)
      (Set.Subset.refl _) (b65z_s₀ c)) :
    let E := b63e_transportMap c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
      D.P (b65z_s₀ c) t
    E (b63g2_centre c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c) x) =
      b4_latticeAct ℂ (C := b65z_fibre c D.C t) b63d_scalarElement (E x) := by
  change D.P t (b6m_H1Equiv _
    (b63d_centre c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c) x.val)) = _
  rw [b63d_centre_transport c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) t (b65z_s₀ c),
    b63g2_period_centre c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) t
      (D.hG t) (D.P t) (D.hP t), b63d_period_centre_scalar]
  rfl

theorem g32y_reference_operator_transport {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (x : b63l_parameterLattice c D.C D.hC (b6t_polydisc c)
      (Set.Subset.refl _) (b65z_s₀ c)) :
    let E := b63e_transportMap c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
      D.P (b65z_s₀ c) t
    E (b63g2_operator c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c) x) =
      E x + (2 : ℤ) • b4_latticeAct ℂ (C := b65z_fibre c D.C t) b63d_scalarElement (E x) := by
  let E := b63e_transportMap c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
    D.P (b65z_s₀ c) t
  dsimp only [b63g2_operator]
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
    two_nsmul, two_zsmul, map_add]
  exact congrArg (fun y ↦ E x + (y + y)) (g32y_reference_centre_transport D t x)

end HodgeLean.Foundations.Program

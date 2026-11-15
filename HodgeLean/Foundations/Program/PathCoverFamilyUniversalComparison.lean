import HodgeLean.Foundations.Program.PathCoverFamilyComparison

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

set_option maxHeartbeats 400000 in
theorem b65z_universal_form (τ : g32m_Domain) :
    b60b_form τ = b63g_modelForm b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
      ((b60_riemann_iff τ).2 τ.property) := by
  ext l k
  rfl

set_option maxHeartbeats 400000 in
theorem b65z_universal_bivector (τ : g32m_Domain) :
    polarizationVec (torusCohomology_cupProductOf (b60b_model τ)) (b60b_pol τ) =
      polarizationVec (torusCohomology_cupProductOf (b60b_model τ))
        (latticeClassHQ (b60b_model τ) (b2_bilinToAddHom
          (b63g_modelForm b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
            ((b60_riemann_iff τ).2 τ.property)))) := by
  exact congrArg (fun B : LinearMap.BilinForm ℤ (b2_abelianLattice (b60b_model τ)) ↦
    polarizationVec (torusCohomology_cupProductOf (b60b_model τ))
      (latticeClassHQ (b60b_model τ) (b2_bilinToAddHom B))) (b65z_universal_form τ)

set_option maxHeartbeats 400000 in
theorem b65z_universal_rational_form (τ : g32m_Domain) (v w : ℚ ⊗[ℤ] b60_Lattice) :
    HodgeLean.Foundations.Symplectic.dualForm ((b60b_member τ).nondegenerate)
      (b64e_model_rational b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
        ((b60_riemann_iff τ).2 τ.property) v)
      (b64e_model_rational b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
        ((b60_riemann_iff τ).2 τ.property) w) = b60_E.baseChange ℚ v w := by
  let q := b63g_modelForm b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
    ((b60_riemann_iff τ).2 τ.property)
  let n := b2_abelian_nondegenerate (b60b_model τ) q
    (b63g_modelForm_riemann b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
      ((b60_riemann_iff τ).2 τ.property))
  have hn := b60b_dualForm_congr (b65z_universal_bivector τ) ((b60b_member τ).nondegenerate) n
  let eu := b64e_model_rational b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
    ((b60_riemann_iff τ).2 τ.property)
  have h := b64e_model_rational_form b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
    ((b60_riemann_iff τ).2 τ.property) v w
  exact (congrArg (fun B : LinearMap.BilinForm ℚ (HQ (b60b_model τ) 1) ↦ B (eu v) (eu w)) hn).trans h

end HodgeLean.Foundations.Program

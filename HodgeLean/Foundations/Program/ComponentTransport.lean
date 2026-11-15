import HodgeLean.Foundations.Program.ComponentTransportProofs

/-! # Polarized component transport
Implication from a geometric Hurwitz chart chain to integral transport. Compatible markings
give biholomorphic period coordinates. The certified-chain, marking and polarization
suppliers are set aside; their former signatures are in docs/specs/ComponentTransport.md.
Theorem A route inputs remain separate.
HC no distance; AV milestone no distance.
-/
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

attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- Integral transport through a geometric Hurwitz chart chain.
Source: G32 v0.16, Lemma 3.4 and its proof; flat integral homology, the fixed group-ring factor and intersection pairing. -/
theorem b65y_component_transport (H : b65y_HurwitzChain) :
    ∃ e : b65y_lattice (H.chart 0) ≃ₗ[ℤ] b65y_lattice (H.chart (Fin.last H.n)),
      (∀ x, e ((H.chart 0).2.2.A (b65z_s₀ (H.chart 0).1) x) =
        (H.chart (Fin.last H.n)).2.2.A (b65z_s₀ (H.chart (Fin.last H.n)).1) (e x)) ∧
      ∀ x y, b65y_pairing (H.chart (Fin.last H.n)) (e x) (e y) =
        b65y_pairing (H.chart 0) x y :=
  b65y_component_transport_aux H

example := @b65y_component_transport

/-- Compatible rational markings give a biholomorphic change of period coordinates and the derivative chain rule.
Source: G32 v0.16, §2.2 and §3.3; the unitary action on the Hermitian symmetric domain; Mathlib fderiv_comp. -/
theorem b65y_change_marking (c : Fin 10 → ℂ) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ c)).baseChange ℚ y) = b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
        (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c))).baseChange ℚ y z)
    (m' : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ' : ∀ y, m' ((D.A (b65z_s₀ c)).baseChange ℚ y) = b60_omega.baseChange ℚ (m' y))
    (hpair' : ∀ y z, b60_E.baseChange ℚ (m' y) (m' z) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
        (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c))).baseChange ℚ y z) :
    ∃ Φ : (Fin 9 → ℂ) → (Fin 9 → ℂ),
    ∃ Ψ : (Fin 9 → ℂ) → (Fin 9 → ℂ),
      AnalyticOnNhd ℂ Φ g32m_Domain ∧ AnalyticOnNhd ℂ Ψ g32m_Domain ∧
      MapsTo Φ g32m_Domain g32m_Domain ∧ MapsTo Ψ g32m_Domain g32m_Domain ∧
      (∀ z ∈ g32m_Domain, Ψ (Φ z) = z ∧ Φ (Ψ z) = z) ∧
      (∀ z ∈ g32m_Domain, IsUnit (fderiv ℂ Φ z)) ∧
      ∀ t ∈ b6t_polydisc c,
        b65z_period D (b65z_s₀ c) m' t = Φ (b65z_period D (b65z_s₀ c) m t) ∧
        fderiv ℂ (b65z_period D (b65z_s₀ c) m') t =
          (fderiv ℂ Φ (b65z_period D (b65z_s₀ c) m t)).comp
            (fderiv ℂ (b65z_period D (b65z_s₀ c) m) t) :=
  b65y_change_marking_aux c g hg D m hJ hpair m' hJ' hpair'

example := @b65y_change_marking

end HodgeLean.Foundations.Program

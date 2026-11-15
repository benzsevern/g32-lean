import HodgeLean.Foundations.Program.ComponentTransportUnlabelledProofs

/-! # Component transport at the G32 centre: unlabelled form
Integral transport through an unlabelled Hurwitz chart chain. The certified chain and the
consumer statements built on it are set aside in `ComponentTransportUnlabelledSetAside.lean`,
off `main`; the consumers with an explicit chain binder are in
`ComponentTransportUnlabelledProofs.lean`.
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

/-- Integral transport through an unlabelled geometric Hurwitz chart chain.
Source: G32 v0.16, Lemma 3.4 and its proof; `b65y_overlap_transport`, which accepts independent parameters on the two charts. -/
theorem b65y_component_transport_u (H : b65y_UnlabelledHurwitzChain) :
    ∃ e : b65y_lattice (H.chart 0) ≃ₗ[ℤ] b65y_lattice (H.chart (Fin.last H.n)),
      (∀ x, e ((H.chart 0).2.2.A (b65z_s₀ (H.chart 0).1) x) =
        (H.chart (Fin.last H.n)).2.2.A (b65z_s₀ (H.chart (Fin.last H.n)).1) (e x)) ∧
      ∀ x y, b65y_pairing (H.chart (Fin.last H.n)) (e x) (e y) =
        b65y_pairing (H.chart 0) x y :=
  b65y_component_transport_u_aux H

example := @b65y_component_transport_u

end HodgeLean.Foundations.Program

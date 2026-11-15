import HodgeLean.Foundations.Program.ComponentTransportDefs

/-! # Component transport: unlabelled chart chains
Finite chains of retained Hurwitz charts in which adjacent charts identify filled fibres at
separately labelled parameters. The gluing is an equivariant biholomorphism; it need not
commute with the quotient projections, so it may relabel the branch points. No lattice
comparison or period comparison is part of this data.
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

/-- A finite path through retained Hurwitz charts in the unlabelled Hurwitz space. Adjacent
charts carry one parameter each, in their own polydiscs, and an equivariant biholomorphic
identification of the filled fibres at those parameters.
Source: G32 v0.16, §3.1 and proof of Lemma 3.4; review hlean-rev-htw (2026-11-05),
`docs/specs/spec-htw.md` on `spec/htw`, unlabelled chain interface. -/
structure b65y_UnlabelledHurwitzChain where
  n : ℕ
  chart : Fin (n + 1) → b65y_Chart
  overlap : (i : Fin n) →
    b6t_polydisc (chart i.castSucc).1 ×
    b6t_polydisc (chart i.succ).1
  glue : (i : Fin n) →
    b65z_fibre (chart i.castSucc).1 (chart i.castSucc).2.2.C
      (overlap i).1 ≃ₜ
    b65z_fibre (chart i.succ).1 (chart i.succ).2.2.C
      (overlap i).2
  hol : ∀ i, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (glue i)
  inv_hol : ∀ i, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (glue i).symm
  equivariant : ∀ i (g : b4b_Group) x,
    glue i (g • x) = g • glue i x

example (d : b65y_Chart) : b65y_UnlabelledHurwitzChain :=
  ⟨0, fun _ ↦ d, (fun i ↦ i.elim0), (fun i ↦ i.elim0), (fun i ↦ i.elim0), (fun i ↦ i.elim0), (fun i ↦ i.elim0)⟩

/-- A labelled chain is an unlabelled chain whose two overlap parameters coincide.
Source: `b65y_HurwitzChain`; review hlean-rev-htw (2026-11-05). -/
def b65y_unlabelled_of_chain (H : b65y_HurwitzChain) : b65y_UnlabelledHurwitzChain where
  n := H.n
  chart := H.chart
  overlap i := (⟨(H.overlap i).val, (H.overlap i).property.1⟩,
    ⟨(H.overlap i).val, (H.overlap i).property.2⟩)
  glue := H.glue
  hol := H.hol
  inv_hol := H.inv_hol
  equivariant := H.equivariant

example (H : b65y_HurwitzChain) : (b65y_unlabelled_of_chain H).chart = H.chart := rfl

end HodgeLean.Foundations.Program

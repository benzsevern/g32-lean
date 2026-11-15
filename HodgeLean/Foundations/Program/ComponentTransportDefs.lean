import HodgeLean.Foundations.Program.BraidBridgesDefs
import HodgeLean.Foundations.Program.PathCoverFamily
import HodgeLean.Foundations.Program.PrymFiberPolarization

/-! # Component transport: geometric chart chains
Finite chains of retained Hurwitz charts glued by equivariant biholomorphisms of overlap
fibres. No lattice comparison or period comparison is part of this data.
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


/-- A retained Hurwitz chart with its centre and ordered rotation tuple.
Source: G32 v0.16, §3.1; `b65z_SharedFamily`. -/
abbrev b65y_Chart := Σ c : Fin 10 → ℂ, Σ g : Fin 13 → b4b_Group, b65z_SharedFamily c g

example (c : Fin 10 → ℂ) (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily c g) :
    b65y_Chart := ⟨c, g, D⟩

/-- An integral reference lattice of a retained chart.
Source: `b63l_parameterLattice`, G32 v0.16, proof of Lemma 3.4. -/
abbrev b65y_lattice (d : b65y_Chart) :=
  b63l_parameterLattice d.1 d.2.2.C d.2.2.hC (b6t_polydisc d.1) (Subset.refl _) (b65z_s₀ d.1)

example (d : b65y_Chart) : Module ℤ (b65y_lattice d) := inferInstance

/-- The original intersection pairing on the reference lattice.
Source: `b63e_singularQ`, G32 v0.16, proof of Lemma 3.4. -/
abbrev b65y_pairing (d : b65y_Chart) : LinearMap.BilinForm ℤ (b65y_lattice d) :=
  b63e_singularQ d.1 d.2.2.C d.2.2.hC (b6t_polydisc d.1) (Subset.refl _)
    (b65z_s₀ d.1) (d.2.2.P (b65z_s₀ d.1)) (d.2.2.Q (b65z_s₀ d.1))

example (d : b65y_Chart) (x y : b65y_lattice d) : ℤ := b65y_pairing d x y

/-- A finite geometric path through retained Hurwitz charts. Adjacent charts have a common
configuration and equivariant biholomorphic identifications of the filled fibres there.
The straight segments inside each polydisc join its centre to the overlap parameters.
Source: G32 v0.16, §3.1 and proof of Lemma 3.4; local trivializations of the Hurwitz family. -/
structure b65y_HurwitzChain where
  n : ℕ
  chart : Fin (n + 1) → b65y_Chart
  overlap : (i : Fin n) → {t : Fin 10 → ℂ //
    t ∈ b6t_polydisc (chart i.castSucc).1 ∧ t ∈ b6t_polydisc (chart i.succ).1}
  glue : (i : Fin n) →
    b65z_fibre (chart i.castSucc).1 (chart i.castSucc).2.2.C
      ⟨(overlap i).val, (overlap i).property.1⟩ ≃ₜ
    b65z_fibre (chart i.succ).1 (chart i.succ).2.2.C
      ⟨(overlap i).val, (overlap i).property.2⟩
  hol : ∀ i, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (glue i)
  inv_hol : ∀ i, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (glue i).symm
  equivariant : ∀ i (g : b4b_Group) x, glue i (g • x) = g • glue i x

example (d : b65y_Chart) : b65y_HurwitzChain :=
  ⟨0, fun _ ↦ d, (fun i ↦ i.elim0), (fun i ↦ i.elim0), (fun i ↦ i.elim0), (fun i ↦ i.elim0), (fun i ↦ i.elim0)⟩

end HodgeLean.Foundations.Program

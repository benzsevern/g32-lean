import HodgeLean.Foundations.Program.CodifferentialDictionaryBoundaryProofs

noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

open Metric Matrix

def b66d_branchPoles {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) : Finset D.C := (b66d_branch_preimage_finite D).toFinset

theorem b66d_standard_velocity_splittings {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    (∀ k a z, z ∈ b66f_domain D t a → MeromorphicAt (b66d_branchLift D k a) z) ∧
    (∀ k a z, z ∈ b66f_domain D t a →
      ((D.atlas.A a).symm (t.val, z)).2 ∉ b66d_branchPoles D →
        AnalyticAt ℂ (b66d_branchLift D k a) z) ∧
    ∀ k a b x, x ∉ b66d_branchPoles D → (t, x) ∈ (D.atlas.A a).source →
      (t, x) ∈ (D.atlas.A b).source →
      b66f_cocycle D t (Pi.single k 1) a b x =
        b66f_boundary D t (b66d_branchLift D k) a b x := by
  refine ⟨fun k a z hz => b66d_branchLift_meromorphic D k a z, ?_, ?_⟩
  · intro k a z hz hx
    apply b66d_branchLift_analytic D t k a z hz
    simpa only [b66d_branchPoles, Set.Finite.mem_toFinset, Set.mem_preimage] using hx
  · intro k a b x hx ha hb
    apply b66d_branchLift_boundary D t k a b x _ ha hb
    simpa only [b66d_branchPoles, Set.Finite.mem_toFinset, Set.mem_preimage] using hx

end HodgeLean.Foundations.Program

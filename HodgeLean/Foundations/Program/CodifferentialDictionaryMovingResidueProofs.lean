import HodgeLean.Foundations.Program.CodifferentialDictionaryMarkedResidueProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryBranchRowProofs

import HodgeLean.Foundations.Program.CoverDictionaryCharts

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
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b66d_moving_product_residue (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    {θ : ℂ} (hθ : θ ∈ ball (0 : ℂ) O.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : D.C) (k : Fin 10)
    (hk : D.atlas.f x = b6_branch (b65z_centre p) (Fin.castLE (by norm_num) k))
    (N : Fin 10 → ℂ) (cj : Bool)
    (φ : b65g_homG D t cj) (ψ : b65g_homG D t (!cj))
    (q r : b66f_primitiveForms D t)
    (hq : b66f_chartForm D t q.val = φ.val (Pi.single 0 1))
    (hr : b66f_chartForm D t r.val = ψ.val (Pi.single 0 1))
    (hnum : ∀ u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t),
      u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
      b65g_contract φ.val ψ.val u = b65g_quadratic D t
        (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) N u) :
    TauCeti.Contour.residue
      (fun z => b66d_branchLift D k (t, x) z *
        b66f_multiply D t q r (t, x) ((D.atlas.A (t, x)).symm (t.val, z)).2)
      (D.atlas.A (t, x) (t, x)).2 =
      (D.atlas.n x : ℂ) / 4 * (N ᵥ* b65g_branchMatrix p θ) k := by
  obtain ⟨hs, hab, hR, ha, hb⟩ := b65g_point_facts p O hθ k
  rw [b66d_branch_row_evaluation p O hθ]
  apply b66d_marked_product_residue D t _ _ ⟨(t, x), rfl⟩ k hk (b65p_poles p θ) N
    (mul_ne_zero ha hb) (sub_ne_zero.mpr hab.symm) hs hR _ _ cj φ ψ q r hq hr hnum
  · rw [ht]
    rfl
  · exact ⟨Sum.inl 0, rfl⟩

end HodgeLean.Foundations.Program

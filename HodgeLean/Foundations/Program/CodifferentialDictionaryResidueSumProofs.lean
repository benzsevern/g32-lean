import HodgeLean.Foundations.Program.CodifferentialDictionaryMovingResidueProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryDegreeProofs

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

theorem b66d_product_residue_sum (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    {θ : ℂ} (hθ : θ ∈ ball (0 : ℂ) O.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (k : Fin 10)
    (N : Fin 10 → ℂ) (cj : Bool)
    (φ : b65g_homG D t cj) (ψ : b65g_homG D t (!cj))
    (q r : b66f_primitiveForms D t)
    (hq : b66f_chartForm D t q.val = φ.val (Pi.single 0 1))
    (hr : b66f_chartForm D t r.val = ψ.val (Pi.single 0 1))
    (hnum : ∀ u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t),
      u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
      b65g_contract φ.val ψ.val u = b65g_quadratic D t
        (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) N u) :
    b66f_residueSum D t (b66d_branchPoles D) (b66d_branchLift D k)
      (b66f_multiply D t q r) = (38880 : ℂ) * (N ᵥ* b65g_branchMatrix p θ) k := by
  let T := (b66d_branchPoles D).filter
    (fun x => D.atlas.f x = b6_branch (b65z_centre p) (Fin.castLE (by norm_num) k))
  let R := (N ᵥ* b65g_branchMatrix p θ) k
  have hsum : b66f_residueSum D t (b66d_branchPoles D) (b66d_branchLift D k)
      (b66f_multiply D t q r) = ∑ x ∈ T, (D.atlas.n x : ℂ) / 4 * R := by
    unfold b66f_residueSum
    rw [show T = _ from rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hk : D.atlas.f x = b6_branch (b65z_centre p) (Fin.castLE (by norm_num) k)
    · rw [if_pos hk]
      exact b66d_moving_product_residue p O D hθ t ht x k hk N cj φ ψ q r hq hr hnum
    · rw [if_neg hk]
      simp only [b66d_branchLift, hk, if_false, zero_mul]
      exact TauCeti.Contour.residue_eq_zero_of_analyticAt analyticAt_const
  have hdeg : (∑ x ∈ T, (D.atlas.n x : ℂ)) = 155520 := by
    exact_mod_cast b66d_branch_degree D t (Fin.castLE (by norm_num) k)
  rw [hsum]
  calc
    (∑ x ∈ T, (D.atlas.n x : ℂ) / 4 * R) =
        (∑ x ∈ T, (D.atlas.n x : ℂ)) * (R / 4) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (38880 : ℂ) * R := by rw [hdeg]; ring

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.CodifferentialDictionaryMarkedGermProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryPolynomialResidueProofs

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

theorem b66d_marked_product_residue {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a b : ℂ)
    (p : b65z_fibre c D.C t) (k : Fin 10)
    (hk : D.atlas.f p.val.2 = b6_branch c (Fin.castLE (by norm_num) k))
    (poles : Fin 4 ⊕ Fin 12 → ℂ) (N : Fin 10 → ℂ)
    (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (hs : poles (Sum.inr (Fin.castLE (by norm_num) k)) ≠ 0)
    (hR : b65g_rest poles (Fin.castLE (by norm_num) k)
      (poles (Sum.inr (Fin.castLE (by norm_num) k))) ≠ 0)
    (ht : t.val k = b65s_normalize a b (poles (Sum.inr (Fin.castLE (by norm_num) k))))
    (h0 : (0 : ℂ) ∈ Set.range poles)
    (cj : Bool) (φ : b65g_homG D t cj) (ψ : b65g_homG D t (!cj))
    (q r : b66f_primitiveForms D t)
    (hq : b66f_chartForm D t q.val = φ.val (Pi.single 0 1))
    (hr : b66f_chartForm D t r.val = ψ.val (Pi.single 0 1))
    (hnum : ∀ u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t),
      u.1 ∈ b65g_good D t a b poles →
      b65g_contract φ.val ψ.val u = b65g_quadratic D t a b poles N u) :
    TauCeti.Contour.residue
      (fun z => b66d_branchLift D k p.val z *
        b66f_multiply D t q r p.val ((D.atlas.A p.val).symm (t.val, z)).2)
      (D.atlas.A p.val p.val).2 =
      (D.atlas.n p.val.2 : ℂ) / 4 *
        ((∑ j : Fin 10, N j * poles (Sum.inr (Fin.castLE (by norm_num) k)) ^ j.val) /
        (b65g_rest poles (Fin.castLE (by norm_num) k)
          (poles (Sum.inr (Fin.castLE (by norm_num) k))) *
          (a * b / ((b - a) * poles (Sum.inr (Fin.castLE (by norm_num) k)) ^ 2)))) := by
  have hg := b66d_multiply_marked_germ D t a b _ p k hk hab hba hs ht cj φ ψ q r hq hr poles N h0 hnum
  rw [(D.atlas.hmark p.val (Fin.castLE (by norm_num) k) hk).1]
  refine Eq.trans (TauCeti.Contour.residue_congr_nhdsNE ?_) (b66d_polynomial_branch_residue
    a b poles (Fin.castLE (by norm_num) k) N (D.atlas.n p.val.2) hab hba hs hR (D.atlas.hn p.val.2))
  filter_upwards [hg] with z hz
  rw [hz]
  simp only [b66d_branchLift, hk, if_pos, ht]

end HodgeLean.Foundations.Program

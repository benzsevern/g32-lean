import HodgeLean.Foundations.Program.CodifferentialDictionaryOriginalDifferentialProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryAveragedEvaluationProofs

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

theorem b66d_multiply_marked_coefficient {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a b : ℂ)
    (A : b66f_Index D) (k : Fin 10)
    (hk : D.atlas.f A.2 = b6_branch c (Fin.castLE (by norm_num) k))
    (y : b65z_fibre c D.C t) (hy : y.val ∈ (D.atlas.A A).source)
    (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (hw : b - (t.val k + (b66f_gen_b66g_slice D t A y) ^ D.atlas.n A.2) * (b - a) ≠ 0)
    (cj : Bool) (φ : b65g_homG D t cj) (ψ : b65g_homG D t (!cj))
    (q r : b66f_primitiveForms D t)
    (hq : b66f_chartForm D t q.val = φ.val (Pi.single 0 1))
    (hr : b66f_chartForm D t r.val = ψ.val (Pi.single 0 1))
    (poles : Fin 4 ⊕ Fin 12 → ℂ) (N : Fin 10 → ℂ)
    (hD : (b65q_denominator poles).eval (b65g_sFun D t a b y) ≠ 0)
    (hnum : b65g_contract φ.val ψ.val ⟨y, (1 : ℂ)⟩ =
      b65g_quadratic D t a b poles N ⟨y, (1 : ℂ)⟩) :
    b66f_multiply D t q r A y.val.2 =
      (1 / 4 : ℂ) * (∑ j : Fin 10, N j * (b65g_sFun D t a b y) ^ j.val) /
        (b65q_denominator poles).eval (b65g_sFun D t a b y) *
      ((b65g_sFun D t a b y) ^ 2 / (a * b / (b - a)) *
        ((D.atlas.n A.2 : ℂ) * (b66f_gen_b66g_slice D t A y) ^ (D.atlas.n A.2 - 1))) ^ 2 := by
  have havg := b66d_averaged_product_evaluation D t cj φ ψ q r hq hr A y hy 1
  have hd := b66d_ds_marked_chart D t a b A k hk y hy hab hba hw 1
  have hne := b66f_gen_b66g_slice_ne D t A y hy
  apply mul_right_cancel₀ (pow_ne_zero 2 hne)
  rw [havg, hnum]
  unfold b65g_quadratic
  rw [b66d_numerator_fraction_evaluation N poles _ hD, hd]
  ring

end HodgeLean.Foundations.Program

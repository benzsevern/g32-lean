import HodgeLean.Foundations.Program.CodifferentialDictionaryAverageProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryRamificationProofs

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

def b66d_branchLift {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (k : Fin 10) (a : b66f_Index D) (z : ℂ) : ℂ :=
  if D.atlas.f a.2 = b6_branch c (Fin.castLE (by norm_num) k) then
    ((D.atlas.n a.2 : ℂ) * z ^ (D.atlas.n a.2 - 1))⁻¹ else 0

theorem b66d_branchLift_meromorphic {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (k : Fin 10) (a : b66f_Index D) (z : ℂ) :
    MeromorphicAt (b66d_branchLift D k a) z := by
  unfold b66d_branchLift
  split_ifs
  · exact ((analyticAt_const.mul (analyticAt_id.pow _)).meromorphicAt).inv
  · exact analyticAt_const.meromorphicAt

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b66d_branch_preimage_finite {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) :
    (D.atlas.f ⁻¹' Set.range (b6_branch c)).Finite := by
  have hnc : ∃ x y : D.C, D.atlas.f x ≠ D.atlas.f y := by
    obtain ⟨x, hx⟩ := D.atlas.hsurj ((0 : ℂ) : OnePoint ℂ)
    obtain ⟨y, hy⟩ := D.atlas.hsurj ((1 : ℂ) : OnePoint ℂ)
    refine ⟨x, y, ?_⟩
    rw [hx, hy]
    exact OnePoint.coe_injective.ne (by norm_num)
  have hf (j : Fin 13) : (D.atlas.f ⁻¹' {b6_branch c j}).Finite :=
    b4_fiber_finite (by simp) (by simp) D.atlas.f D.atlas.hf hnc _
  have h := Set.finite_iUnion hf
  convert h using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_range, Set.mem_iUnion, Set.mem_singleton_iff,
    eq_comm]

theorem b66d_branchChart_nonzero {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a : b66f_Index D)
    (j : Fin 13) (heq : D.atlas.f a.2 = b6_branch c j)
    (z : ℂ) (hz : z ∈ b66f_domain D t a)
    (hreg : D.atlas.f ((D.atlas.A a).symm (t.val, z)).2 ∉ Set.range (b6_branch c)) :
    z ≠ 0 := by
  intro hz0
  have hm := (D.atlas.hmark a j heq).2
    ((D.atlas.A a).symm (t.val, z)) ((D.atlas.A a).map_target hz)
  simp only [b6a_map] at hm
  rw [b66f_gen_b66k_inverse_parameter D a _ hz] at hm
  have hcoord : (D.atlas.A a ((D.atlas.A a).symm (t.val, z))).2 = z :=
    congrArg Prod.snd ((D.atlas.A a).right_inv hz)
  have hpow : z ^ D.atlas.n a.2 = 0 := by
    rw [hz0, zero_pow (Nat.ne_of_gt (D.atlas.hn a.2))]
  rw [hcoord, hpow, b6a_value_zero] at hm
  obtain ⟨E, hE⟩ := b6t_homeomorph c D.atlas.hb t.val t.property
  have hb : D.atlas.f ((D.atlas.A a).symm (t.val, z)).2 =
      b6_branch c j := by
    apply E.injective
    simpa only [hE, b6t_marks c D.atlas.hb t.val t.property] using hm
  exact hreg ⟨_, hb.symm⟩

theorem b66d_branchLift_analytic {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (k : Fin 10)
    (a : b66f_Index D) (z : ℂ) (hz : z ∈ b66f_domain D t a)
    (hreg : D.atlas.f ((D.atlas.A a).symm (t.val, z)).2 ∉ Set.range (b6_branch c)) :
    AnalyticAt ℂ (b66d_branchLift D k a) z := by
  unfold b66d_branchLift
  split_ifs with heq
  · have hn : (D.atlas.n a.2 : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (D.atlas.hn a.2))
    have hzne := b66d_branchChart_nonzero D t a
      (Fin.castLE (by norm_num) k) heq z hz hreg
    exact (analyticAt_const.mul (analyticAt_id.pow _)).inv
      (mul_ne_zero hn (pow_ne_zero _ hzne))
  · exact analyticAt_const

end HodgeLean.Foundations.Program

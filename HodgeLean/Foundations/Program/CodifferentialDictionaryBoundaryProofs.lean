import HodgeLean.Foundations.Program.CodifferentialDictionaryLiftDifferentialProofs

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

theorem b66d_branchLift_boundary {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (k : Fin 10)
    (a b : b66f_Index D) (x : D.C)
    (hreg : D.atlas.f x ∉ Set.range (b6_branch c))
    (ha : (t, x) ∈ (D.atlas.A a).source) (hb : (t, x) ∈ (D.atlas.A b).source) :
    b66f_cocycle D t (Pi.single k 1) a b x =
      b66f_boundary D t (b66d_branchLift D k) a b x := by
  let u := D.atlas.A a (t, x)
  let v := D.atlas.A b (t, x)
  have hua : u ∈ (D.atlas.A a).target := (D.atlas.A a).map_source ha
  have hvb : v ∈ (D.atlas.A b).target := (D.atlas.A b).map_source hb
  have hpaira : (t.val, u.2) = u := Prod.ext (D.atlas.hparam a _ ha).symm rfl
  have hpairb : (t.val, v.2) = v := Prod.ext (D.atlas.hparam b _ hb).symm rfl
  have hia : (D.atlas.A a).symm (t.val, u.2) = (t, x) := by
    rw [hpaira]
    exact (D.atlas.A a).left_inv ha
  have hib : (D.atlas.A b).symm (t.val, v.2) = (t, x) := by
    rw [hpairb]
    exact (D.atlas.A b).left_inv hb
  obtain ⟨Fa, hFa, hFaz, hFak⟩ := b66d_projectionCoeff_lift_differential D t a u.2
    (by change (t.val, u.2) ∈ (D.atlas.A a).target; rwa [hpaira]) (by rwa [hia])
  obtain ⟨Fb, hFb, hFbz, hFbk⟩ := b66d_projectionCoeff_lift_differential D t b v.2
    (by change (t.val, v.2) ∈ (D.atlas.A b).target; rwa [hpairb]) (by rwa [hib])
  have hFa' : HasFDerivAt (b66d_projectionCoeff D a) Fa u := by rwa [hpaira] at hFa
  have hub : (D.atlas.A a).symm u ∈ (D.atlas.A b).source := by
    rw [(D.atlas.A a).left_inv ha]
    exact hb
  have htrans : (u.1, b66f_transition D a b u) = (t.val, v.2) := by
    apply Prod.ext
    · exact D.atlas.hparam a _ ha
    · change (D.atlas.A b ((D.atlas.A a).symm u)).2 = v.2
      rw [(D.atlas.A a).left_inv ha]
  have hFb' : HasFDerivAt (b66d_projectionCoeff D b) Fb
      (u.1, b66f_transition D a b u) := by rwa [htrans]
  have hT := (b66f_gen_b66k_transition_analytic D a b u ⟨hua, hub⟩).differentiableAt.hasFDerivAt
  have he := b66d_lift_overlap (b66d_projectionCoeff D a) (b66d_projectionCoeff D b)
    (b66f_transition D a b) Fa Fb _ u (Pi.single k 1) hFa' hFb' hT
    (b66d_projectionCoeff_transition_eventually D a b u hua hub) hFaz hFbz
  rw [hFak, hFbk] at he
  simpa only [b66f_cocycle, LinearMap.coe_mk, AddHom.coe_mk, b66f_boundary,
    ite_eq_left (show (t, x) ∈ (D.atlas.A a).source ∩ (D.atlas.A b).source from ⟨ha, hb⟩),
    b66f_vertical, u, v] using he

end HodgeLean.Foundations.Program

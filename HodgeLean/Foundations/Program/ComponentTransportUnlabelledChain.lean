import HodgeLean.Foundations.Program.ComponentTransportUnlabelledDefs
import HodgeLean.Foundations.Program.ComponentTransportCertifiedChain

/-! # Unlabelled chain: edges and walks
Single edges between retained charts at separately labelled parameters, finite walks of such
edges and their conversion to a `b65y_UnlabelledHurwitzChain`. Labelled edges and walks embed.
No lattice comparison is part of this data.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- One edge of an unlabelled chart chain: a parameter in each polydisc and an equivariant
biholomorphism of the two filled fibres there.
Source: `b65y_UnlabelledHurwitzChain`; review hlean-rev-htw (2026-11-05). -/
structure b65y_UnlabelledEdge (d₀ d₁ : b65y_Chart) where
  t₀ : b6t_polydisc d₀.1
  t₁ : b6t_polydisc d₁.1
  glue : b65z_fibre d₀.1 d₀.2.2.C t₀ ≃ₜ b65z_fibre d₁.1 d₁.2.2.C t₁
  hol : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω glue
  inv_hol : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω glue.symm
  equivariant : ∀ (g : b4b_Group) x, glue (g • x) = g • glue x

/-- A labelled edge is an unlabelled edge at equal parameters.
Source: `b65y_Edge`, `b65y_UnlabelledEdge`; the same embedding as `b65y_unlabelled_of_chain`. -/
def b65y_unlabelledEdge_of_edge {d₀ d₁ : b65y_Chart} (E : b65y_Edge d₀ d₁) :
    b65y_UnlabelledEdge d₀ d₁ where
  t₀ := E.t
  t₁ := ⟨E.t.val, E.ht₁⟩
  glue := E.glue
  hol := E.hol
  inv_hol := E.inv_hol
  equivariant := E.equivariant

example (d : b65y_Chart) : (b65y_unlabelledEdge_of_edge (b65y_Edge.refl d)).t₀ =
    (b65y_Edge.refl d).t := rfl

/-- A finite walk of unlabelled edges between retained charts.
Source: `b65y_UnlabelledHurwitzChain`; finite composition of chart edges. -/
inductive b65y_UnlabelledWalk : b65y_Chart → b65y_Chart → Type 1
  | nil (d : b65y_Chart) : b65y_UnlabelledWalk d d
  | cons {d₀ d₁ d₂ : b65y_Chart} : b65y_UnlabelledEdge d₀ d₁ → b65y_UnlabelledWalk d₁ d₂ →
      b65y_UnlabelledWalk d₀ d₂

/-- Concatenation of unlabelled walks.
Source: `b65y_UnlabelledWalk`; concatenation of finite edge sequences. -/
def b65y_UnlabelledWalk.append : {d₀ d₁ d₂ : b65y_Chart} → b65y_UnlabelledWalk d₀ d₁ →
    b65y_UnlabelledWalk d₁ d₂ → b65y_UnlabelledWalk d₀ d₂
  | _, _, _, .nil _, w => w
  | _, _, _, .cons e v, w => .cons e (v.append w)

example (d₀ d₁ : b65y_Chart) (w : b65y_UnlabelledWalk d₀ d₁) :
    (b65y_UnlabelledWalk.nil d₀).append w = w := rfl

/-- A labelled walk is an unlabelled walk with the same edges.
Source: `b65y_Walk`, `b65y_unlabelledEdge_of_edge`; edgewise embedding. -/
def b65y_unlabelledWalk_of_walk : {d₀ d₁ : b65y_Chart} → b65y_Walk d₀ d₁ →
    b65y_UnlabelledWalk d₀ d₁
  | _, _, .nil d => .nil d
  | _, _, .cons e v => .cons (b65y_unlabelledEdge_of_edge e) (b65y_unlabelledWalk_of_walk v)

example (d : b65y_Chart) : b65y_unlabelledWalk_of_walk (b65y_Walk.nil d) =
    b65y_UnlabelledWalk.nil d := rfl

/-- Prepending an unlabelled edge to an unlabelled chart chain.
Source: `b65y_UnlabelledHurwitzChain`; `Fin.cons` on charts and `Fin.cases` on edges. -/
def b65y_unlabelledChainCons (d : b65y_Chart) (H : b65y_UnlabelledHurwitzChain)
    (E : b65y_UnlabelledEdge d (H.chart 0)) : b65y_UnlabelledHurwitzChain where
  n := H.n + 1
  chart := Fin.cons (α := fun _ ↦ b65y_Chart) d H.chart
  overlap i := Fin.cases (motive := fun i : Fin (H.n + 1) ↦
      b6t_polydisc (Fin.cons (α := fun _ ↦ b65y_Chart) d H.chart i.castSucc : b65y_Chart).1 ×
      b6t_polydisc (Fin.cons (α := fun _ ↦ b65y_Chart) d H.chart i.succ : b65y_Chart).1)
    (E.t₀, E.t₁) (fun j ↦ H.overlap j) i
  glue i := by
    induction i using Fin.cases with
    | zero => exact E.glue
    | succ j => exact H.glue j
  hol i := by
    induction i using Fin.cases with
    | zero => exact E.hol
    | succ j => exact H.hol j
  inv_hol i := by
    induction i using Fin.cases with
    | zero => exact E.inv_hol
    | succ j => exact H.inv_hol j
  equivariant i := by
    induction i using Fin.cases with
    | zero => exact E.equivariant
    | succ j => exact H.equivariant j

example (d : b65y_Chart) (H : b65y_UnlabelledHurwitzChain)
    (E : b65y_UnlabelledEdge d (H.chart 0)) :
    (b65y_unlabelledChainCons d H E).chart 0 = d ∧
      (b65y_unlabelledChainCons d H E).n = H.n + 1 := ⟨rfl, rfl⟩

/-- A walk of unlabelled edges gives an unlabelled chart chain with the same end charts.
Source: `b65y_UnlabelledHurwitzChain`; induction on the walk. -/
theorem b65y_unlabelled_chain_of_walk {d₀ d₁ : b65y_Chart} (w : b65y_UnlabelledWalk d₀ d₁) :
    ∃ H : b65y_UnlabelledHurwitzChain, H.chart 0 = d₀ ∧ H.chart (Fin.last H.n) = d₁ := by
  induction w with
  | nil d =>
    exact ⟨⟨0, fun _ ↦ d, (fun i ↦ i.elim0), (fun i ↦ i.elim0), (fun i ↦ i.elim0),
      (fun i ↦ i.elim0), (fun i ↦ i.elim0)⟩, rfl, rfl⟩
  | @cons a b c E v ih =>
    obtain ⟨H, h0, h1⟩ := ih
    subst h0 h1
    exact ⟨b65y_unlabelledChainCons a H E, rfl, rfl⟩

/-- A labelled chain between two charts gives an unlabelled chain between them.
Source: `b65y_unlabelled_of_chain`. -/
theorem b65y_unlabelled_of_labelled {d₀ d₁ : b65y_Chart}
    (h : ∃ H : b65y_HurwitzChain, H.chart 0 = d₀ ∧ H.chart (Fin.last H.n) = d₁) :
    ∃ H : b65y_UnlabelledHurwitzChain, H.chart 0 = d₀ ∧ H.chart (Fin.last H.n) = d₁ := by
  obtain ⟨H, h0, h1⟩ := h
  exact ⟨b65y_unlabelled_of_chain H, h0, h1⟩

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.HurwitzPrymRexCover
import HodgeLean.Foundations.Program.HurwitzPrymCovConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: good neighborhoods on a punctured surface

Chart balls are good sets: a ball is convex, hence contractible, so two paths in it with the same
endpoints are homotopic; their images under the inverse chart are homotopic in `Y ∖ B`. A connected
Riemann surface minus finitely many points is path-connected. Hence `Y ∖ B` carries the Galois
covering of any surjection `π₁ → Gᵐᵒᵖ`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Topology Metric Set

namespace HodgeLean.Foundations.Program

namespace HurwitzPrymRexCover

variable {Y : Type} [TopologicalSpace Y]

/-- **Chart balls are good** in `Y ∖ B`, and they are arbitrarily small. -/
theorem good_nhds (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E'] [ChartedSpace E' Y]
    [T2Space Y] {B : Set Y} (hB : B.Finite) (x : {y : Y // y ∉ B})
    (N : Set {y : Y // y ∉ B}) (hN : N ∈ 𝓝 x) :
    ∃ V, Good V ∧ x ∈ V ∧ V ⊆ N := by
  set φ := chartAt E' x.1
  obtain ⟨N', hN', hN'N⟩ := (mem_nhds_induced Subtype.val x N).1 hN
  set O : Set Y := interior N' ∩ Bᶜ ∩ φ.source with hO
  have hOo : IsOpen O := (isOpen_interior.inter hB.isClosed.isOpen_compl).inter φ.open_source
  have hxO : x.1 ∈ O := ⟨⟨mem_interior_iff_mem_nhds.2 hN', x.2⟩, mem_chart_source E' x.1⟩
  have hTo : IsOpen (φ.target ∩ φ.symm ⁻¹' O) :=
    φ.continuousOn_symm.isOpen_inter_preimage φ.open_target hOo
  have hxT : φ x.1 ∈ φ.target ∩ φ.symm ⁻¹' O := by
    refine ⟨φ.map_source (mem_chart_source E' x.1), ?_⟩
    rw [mem_preimage, φ.left_inv (mem_chart_source E' x.1)]
    exact hxO
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 hTo _ hxT
  have hT : ∀ z ∈ ball (φ x.1) r, z ∈ φ.target ∧ φ.symm z ∈ O := fun z hz ↦ hrT hz
  -- the inverse chart on the ball, into `Y ∖ B`
  let ψ : C(ball (φ x.1) r, {y : Y // y ∉ B}) :=
    ⟨fun z ↦ ⟨φ.symm z, (hT z z.2).2.1.2⟩,
      (φ.continuousOn_symm.comp_continuous continuous_subtype_val
        fun z ↦ (hT z z.2).1).subtype_mk _⟩
  set V : Set {y : Y // y ∉ B} := {y | y.1 ∈ φ.source ∧ φ y.1 ∈ ball (φ x.1) r} with hV
  have hVo : IsOpen V :=
    continuous_subtype_val.isOpen_preimage _ (φ.isOpen_inter_preimage isOpen_ball)
  have hψV : ∀ y (hy : y ∈ V), ψ ⟨φ y.1, hy.2⟩ = y := fun y hy ↦
    Subtype.ext (φ.left_inv hy.1)
  have hrange : V = range ψ := by
    ext y
    constructor
    · intro hy
      exact ⟨_, hψV y hy⟩
    · rintro ⟨z, rfl⟩
      refine ⟨φ.map_target (hT z z.2).1, ?_⟩
      change φ (φ.symm z) ∈ ball (φ x.1) r
      rw [φ.right_inv (hT z z.2).1]
      exact z.2
  have hconv : Convex ℝ (ball (φ x.1) r) := convex_ball _ _
  haveI : ContractibleSpace (ball (φ x.1) r) :=
    hconv.contractibleSpace ⟨φ x.1, mem_ball_self hr⟩
  -- a path in `V`, read in the chart
  let toBall : ∀ {a b : {y : Y // y ∉ B}} (γ : Path a b) (hγ : ∀ t, γ t ∈ V) (ha : a ∈ V)
      (hb : b ∈ V), Path (⟨φ a.1, ha.2⟩ : ball (φ x.1) r) ⟨φ b.1, hb.2⟩ :=
    fun {a b} γ hγ ha hb ↦
      { toFun := fun t ↦ ⟨φ (γ t).1, (hγ t).2⟩
        continuous_toFun := (φ.continuousOn.comp_continuous
          (continuous_subtype_val.comp γ.continuous) fun t ↦ (hγ t).1).subtype_mk _
        source' := by simp
        target' := by simp }
  have hmap : ∀ {a b : {y : Y // y ∉ B}} (γ : Path a b) (hγ : ∀ t, γ t ∈ V) (ha : a ∈ V)
      (hb : b ∈ V), Path.Homotopic.Quotient.mk γ =
        (Path.Homotopic.Quotient.mk ((toBall γ hγ ha hb).map ψ.continuous)).cast
          (hψV a ha).symm (hψV b hb).symm := by
    intro a b γ hγ ha hb
    rw [← Path.Homotopic.Quotient.mk_cast]
    congr 1
    ext t
    exact (congrArg Subtype.val (hψV (γ t) (hγ t))).symm
  refine ⟨V, ⟨hVo, ?_, ?_⟩, ⟨mem_chart_source E' x.1, mem_ball_self hr⟩, ?_⟩
  · rw [hrange, ← image_univ]
    exact isPathConnected_univ.image ψ.continuous
  · intro a b γ γ' hγ hγ'
    have ha : a ∈ V := by simpa using hγ 0
    have hb : b ∈ V := by simpa using hγ 1
    rw [← Path.Homotopic.Quotient.eq, hmap γ hγ ha hb, hmap γ' hγ' ha hb]
    congr 1
    exact Path.Homotopic.Quotient.eq.2
      ((SimplyConnectedSpace.paths_homotopic _ _).map ψ)
  · intro y hy
    apply hN'N
    have := (hT _ hy.2).2
    rw [φ.left_inv hy.1] at this
    exact (interior_subset this.1.1 : y.1 ∈ N')

/-- **`Y ∖ B` is path-connected** for a connected Riemann surface `Y` and finite `B`. -/
theorem pathConnectedSpace_compl (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [ChartedSpace E' Y] [T2Space Y] [ConnectedSpace Y]
    (hE' : Module.finrank ℂ E' = 1) {B : Set Y} (hB : B.Finite) (y₀ : {y : Y // y ∉ B}) :
    PathConnectedSpace {y : Y // y ∉ B} := by
  have hconn : IsPreconnected (univ \ B) :=
    b4cov_isPreconnected_diff_finite isOpen_univ isPreconnected_univ hB
      fun s _ ↦ b4cov_goodPoint hE' s
  have hset : univ \ B = {y : Y | y ∉ B} := by
    ext
    simp
  rw [hset] at hconn
  have : ConnectedSpace {y : Y // y ∉ B} :=
    isConnected_iff_connectedSpace.1 ⟨⟨y₀.1, y₀.2⟩, hconn⟩
  have := ChartedSpace.locallyPathConnectedSpace E' Y
  have : LocallyPathConnectedSpace {y : Y // y ∉ B} :=
    hB.isClosed.isOpen_compl.locallyPathConnectedSpace
  exact PathConnectedSpace.of_locallyPathConnectedSpace

end HurwitzPrymRexCover

end HodgeLean.Foundations.Program

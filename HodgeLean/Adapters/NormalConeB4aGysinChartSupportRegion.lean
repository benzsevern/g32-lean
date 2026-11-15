import HodgeLean.Adapters.NormalConeB4aGysinChartSupportDimension

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- One algebraic open contains the entire holomorphic chart and has the sharp
support dimension bound, after removing ambient components missing the chart. -/
theorem a3b4a_gysin_chart_support_dimension_region
    (Y : Over (Spec (CommRingCat.of ℂ))) [IsNoetherian Y.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (γ : AlgebraicCycle Y.left ℚ) {n c : ℕ}
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) :
    ∃ U : Y.left.Opens, (∀ y ∈ Φ.source, y.underlying ∈ U) ∧
      topologicalKrullDim (reducedClosedSubscheme
        ((a3b4a_classAlgebraicSupport Y.hom γ).preimage U.ι.continuous)) ≤ (n : ℕ) := by
  classical
  let B : Set Y.left := {ξ | ξ ∈ genericPoints Y.left ∧
    ¬ ∃ y ∈ Φ.source, y.underlying ∈ closure ({ξ} : Set Y.left)}
  have hB : B.Finite :=
    (genericPoints.finite (NoetherianSpace.finite_irreducibleComponents (α := Y.left))).subset
      (fun _ h => h.1)
  have hclosed : IsClosed (⋃ ξ ∈ B, closure ({ξ} : Set Y.left)) :=
    hB.isClosed_biUnion (fun _ _ => isClosed_closure)
  let W : Y.left.Opens := ⟨(⋃ ξ ∈ B, closure ({ξ} : Set Y.left))ᶜ, hclosed.isOpen_compl⟩
  have hcontain : ∀ y ∈ Φ.source, y.underlying ∈ W := by
    intro y hy hyB
    obtain ⟨ξ, hξ, hyξ⟩ := Set.mem_iUnion₂.mp hyB
    exact hξ.2 ⟨y, hy, hyξ⟩
  have hheight : ∀ y ∈ W, (↑(Order.height y) : WithBot ℕ∞) ≤ n + c := by
    intro y hy
    let K : irreducibleComponents Y.left :=
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
    let ξ := (genericPoints.ofComponent K).val
    have hξ : ξ ∈ genericPoints Y.left := (genericPoints.ofComponent K).property
    have hyξ : y ∈ closure ({ξ} : Set Y.left) := by
      change y ∈ closure ({(genericPoints.ofComponent K).val} : Set Y.left)
      rw [(genericPoints.isGenericPoint_ofComponent K).def]
      exact mem_irreducibleComponent
    have hmeet : ∃ x ∈ Φ.source, x.underlying ∈ closure ({ξ} : Set Y.left) := by
      by_contra hn
      exact hy (Set.mem_iUnion₂.mpr ⟨ξ, ⟨hξ, hn⟩, hyξ⟩)
    obtain ⟨x, hx, hxξ⟩ := hmeet
    have hξheight : (↑(Order.height ξ) : WithBot ℕ∞) ≤ n + c := by
      simpa only [topologicalKrullDim_cycleComponent, Nat.cast_add] using
        a3b4a_gysin_component_dimension_in_chart Y ξ Φ hΦ x hx hxξ
    have hle : y ≤ ξ := Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr hyξ)
    exact (WithBot.coe_le_coe.mpr (Order.height_mono hle)).trans hξheight
  have hiff : ∀ a b, W.ι a ≤ W.ι b ↔ a ≤ b := by
    intro a b
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact W.ι.isOpenEmbedding.isInducing.specializes_iff
  have hstrict : StrictMono W.ι := fun a b hab =>
    lt_iff_le_not_ge.mpr ⟨(hiff a b).mpr hab.le, fun h => hab.not_ge ((hiff b a).mp h)⟩
  have hWdim : topologicalKrullDim W.toScheme ≤ (n + c : ℕ) := by
    rw [Scheme.topologicalKrullDim_eq_orderKrullDim, Order.krullDim_eq_iSup_height]
    refine iSup_le fun y => ?_
    exact (WithBot.coe_le_coe.mpr
      (Order.height_le_height_apply_of_strictMono W.ι hstrict y)).trans
      (by simpa only [Nat.cast_add] using hheight (W.ι y) y.2)
  let S : Closeds W.toScheme := (a3b4a_classAlgebraicSupport Y.hom γ).preimage W.ι.continuous
  have hS : topologicalKrullDim (reducedClosedSubscheme S) ≤ (n + c - c : ℕ) := by
    apply a3b4a_gysin_support_dimension_of_ambient_bound (n + c) c S hWdim
    intro z hz
    have hco := a3b4a_classAlgebraicSupport_coheight Y.hom γ c hc (W.ι z) hz
    have he := coheight_eq_of_isOpenImmersion (x := z) W.ι
    exact he ▸ hco
  refine ⟨W, hcontain, ?_⟩
  simpa only [Nat.add_sub_cancel] using hS

end HodgeLean.Adapters

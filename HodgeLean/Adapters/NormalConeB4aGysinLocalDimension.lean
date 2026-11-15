import HodgeLean.Adapters.NormalConeB4aGysinComponentChartDimension

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- Bounds on the components through a marked point give an algebraic open
neighborhood with the same dimension bound. -/
theorem a3b4a_gysin_open_dimension_bound_of_components
    {Z : Scheme.{0}} [IsNoetherian Z] (x : Z) (D : ℕ)
    (hD : ∀ ξ : Z, x ∈ closure ({ξ} : Set Z) →
      topologicalKrullDim (cycleComponent Z ξ) ≤ (D : ℕ)) :
    ∃ U : Z.Opens, x ∈ U ∧ topologicalKrullDim U.toScheme ≤ (D : ℕ) := by
  classical
  let B : Set Z := {ξ | ξ ∈ genericPoints Z ∧ x ∉ closure ({ξ} : Set Z)}
  have hB : B.Finite :=
    (genericPoints.finite (NoetherianSpace.finite_irreducibleComponents (α := Z))).subset
      (fun _ h => h.1)
  have hclosed : IsClosed (⋃ ξ ∈ B, closure ({ξ} : Set Z)) :=
    hB.isClosed_biUnion (fun _ _ => isClosed_closure)
  let W : Z.Opens := ⟨(⋃ ξ ∈ B, closure ({ξ} : Set Z))ᶜ, hclosed.isOpen_compl⟩
  have hxW : x ∈ W := by
    intro hxB
    obtain ⟨ξ, hξ, hxξ⟩ := Set.mem_iUnion₂.mp hxB
    exact hξ.2 hxξ
  have hheight : ∀ y ∈ W, (↑(Order.height y) : WithBot ℕ∞) ≤ D := by
    intro y hy
    let K : irreducibleComponents Z :=
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
    let ξ := (genericPoints.ofComponent K).val
    have hξ : ξ ∈ genericPoints Z := (genericPoints.ofComponent K).property
    have hyξ : y ∈ closure ({ξ} : Set Z) := by
      change y ∈ closure ({(genericPoints.ofComponent K).val} : Set Z)
      rw [(genericPoints.isGenericPoint_ofComponent K).def]
      exact mem_irreducibleComponent
    have hxξ : x ∈ closure ({ξ} : Set Z) := by
      by_contra hxnot
      exact hy (Set.mem_iUnion₂.mpr ⟨ξ, ⟨hξ, hxnot⟩, hyξ⟩)
    have hξheight : (↑(Order.height ξ) : WithBot ℕ∞) ≤ D := by
      simpa only [topologicalKrullDim_cycleComponent] using hD ξ hxξ
    have hle : y ≤ ξ := Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr hyξ)
    exact (WithBot.coe_le_coe.mpr (Order.height_mono hle)).trans hξheight
  have hiff : ∀ a b, W.ι a ≤ W.ι b ↔ a ≤ b := by
    intro a b
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact W.ι.isOpenEmbedding.isInducing.specializes_iff
  have hstrict : StrictMono W.ι := fun a b hab =>
    lt_iff_le_not_ge.mpr ⟨(hiff a b).mpr hab.le, fun h => hab.not_ge ((hiff b a).mp h)⟩
  refine ⟨W, hxW, ?_⟩
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun y => ?_
  exact (WithBot.coe_le_coe.mpr
    (Order.height_le_height_apply_of_strictMono W.ι hstrict y)).trans (hheight (W.ι y) y.2)

/-- Every point in the supplied holomorphic chart has an affine algebraic
neighborhood whose dimension is bounded by the chart dimension. -/
theorem a3b4a_gysin_chart_affine_dimension_neighborhood
    (X : Over (Spec (CommRingCat.of ℂ))) [IsNoetherian X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {n c : ℕ}
    (Φ : OpenPartialHomeomorph (ComplexPoint X) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart X.hom Φ) (x : ComplexPoint X) (hx : x ∈ Φ.source) :
    ∃ (U : X.left.Opens) (_ : IsAffineOpen U), x.underlying ∈ U ∧
      topologicalKrullDim U.toScheme ≤ (n + c : ℕ) := by
  obtain ⟨W, hxW, hWdim⟩ := a3b4a_gysin_open_dimension_bound_of_components
    x.underlying (n + c) (fun ξ hxξ =>
      a3b4a_gysin_component_dimension_in_chart X ξ Φ hΦ x hx hxξ)
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hxW
  let k : U.toScheme ⟶ W.toScheme := X.left.homOfLE (U := U) (V := W) (show U ≤ W from hUW)
  letI : IsOpenImmersion k := inferInstanceAs (IsOpenImmersion (X.left.homOfLE (U := U) (V := W) (show U ≤ W from hUW)))
  refine ⟨U, hU, hxU, ?_⟩
  exact k.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hWdim

end HodgeLean.Adapters

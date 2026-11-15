import HodgeLean.Adapters.NormalConeB4aGysinLocalDimension
import HodgeLean.Adapters.NormalConeB4aGysinSupportDimension

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- Algebraic codimension gives the sharp local support dimension bound in the
supplied holomorphic chart, without ambient smoothness. -/
theorem a3b4a_gysin_chart_support_affine_dimension_neighborhood
    (X : Over (Spec (CommRingCat.of ℂ))) [IsNoetherian X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (γ : AlgebraicCycle X.left ℚ) {n c : ℕ}
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (Φ : OpenPartialHomeomorph (ComplexPoint X) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart X.hom Φ) (x : ComplexPoint X) (hx : x ∈ Φ.source) :
    ∃ (U : X.left.Opens) (_ : IsAffineOpen U), x.underlying ∈ U ∧
      topologicalKrullDim (reducedClosedSubscheme
        ((a3b4a_classAlgebraicSupport X.hom γ).preimage U.ι.continuous)) ≤ (n : ℕ) := by
  obtain ⟨U, hU, hxU, hdim⟩ := a3b4a_gysin_chart_affine_dimension_neighborhood X Φ hΦ x hx
  let S : Closeds U.toScheme := (a3b4a_classAlgebraicSupport X.hom γ).preimage U.ι.continuous
  have hS : topologicalKrullDim (reducedClosedSubscheme S) ≤ (n + c - c : ℕ) := by
    apply a3b4a_gysin_support_dimension_of_ambient_bound (n + c) c S hdim
    intro z hz
    have hco := a3b4a_classAlgebraicSupport_coheight X.hom γ c hc (U.ι z) hz
    have he := coheight_eq_of_isOpenImmersion (x := z) U.ι
    exact he ▸ hco
  refine ⟨U, hU, hxU, ?_⟩
  simpa only [Nat.add_sub_cancel] using hS

end HodgeLean.Adapters

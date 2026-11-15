import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedFamilyNormalization

/-! # Actual family cancellation using a chart of one present representative -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- A chart of one active representative suffices for exact cancellation at a point isolating a component of the entire finite family.
Source: Fulton, Intersection Theory, sections 1.5 and 19.1, collection and local cycle normalization.
HC no distance; AV milestone no distance. -/
lemma properCycle_weighted_anchor_chart_cancellation
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (k : ℕ)
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ)
    (a : ∀ i, s2e_supportedClass X (γ i) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) k (a i)) (q : I → ℚ)
    (i₀ : I) (hi₀ : q i₀ ≠ 0) (ξ : X.left) (hξ : ξ ∈ (γ i₀).support)
    (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (heS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom (γ i₀) ↔ (e y).2 = 0)
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ e.source)
    (hxξ : x.underlying ∈ closure ({ξ} : Set X.left))
    (hother : ∀ i η, η ∈ (γ i).support → η ≠ ξ →
      x.underlying ∉ closure ({η} : Set X.left))
    (hcancel : (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) ξ = 0) :
    let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
    let hST : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T :=
      fun i hi y hy => Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩
    ∃ (W : Opens (ComplexPoint X)) (_ : (W : Set (ComplexPoint X)) ⊆ e.source), x ∈ W ∧
      relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) T)
        (SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
          (fun i => a3b4_cycleSupport X.hom (γ i)) T q hST a) = 0 := by
  classical
  dsimp only
  let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
  let hST : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T :=
    fun i hi y hy => Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩
  obtain ⟨O, hOe, hxO, hO⟩ := properCycle_family_component_neighborhood X γ ξ x hother
    (⟨e.source, e.open_source⟩ : Opens (ComplexPoint X)) hx
  let e' := e.restrOpen (O : Set (ComplexPoint X)) O.isOpen
  have he' : a3b4_IsHolChart X.hom e' :=
    a3b4g_isHolChart_restrOpen e he (O : Set (ComplexPoint X)) O.isOpen
  have hprime : ∀ y ∈ e'.source,
      y.underlying ∈ closure ({ξ} : Set X.left) ↔ (e' y).2 = 0 := by
    intro y hy
    exact ((hO i₀ y hy.2).trans (and_iff_right hξ)).symm.trans (heS y hy.1)
  have hT : ∀ y ∈ e'.source, y ∈ T ↔ (e' y).2 = 0 := by
    intro y hy
    refine Iff.trans ?_ (hprime y hy)
    constructor
    · intro hyT
      obtain ⟨i, _, hyi⟩ := Set.mem_iUnion₂.mp hyT
      exact ((hO i y hy.2).mp hyi).2
    · intro hyξ
      exact hST i₀ hi₀ ((hO i₀ y hy.2).mpr ⟨hξ, hyξ⟩)
  obtain ⟨W, hxW, hWe, hW⟩ := properCycle_weighted_isolated_component_cancellation
    X k γ a ha q T hST r e' hT he' x ⟨hx, hxO⟩ ξ hxξ hprime hother hcancel
  exact ⟨W, fun y hy => (hWe hy).1, hxW, hW⟩

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothOpenMultiplicity
import HodgeLean.Adapters.NormalConeB4aGysinBridge2PrescribedChart

/-! # Original chart multiplicity near one ambient smooth affine neighborhood -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Set Filter Topology TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- A single smooth affine neighborhood of the tested point suffices for local constancy of the original multiplicity along any original flattened chart.
Source: Fulton, Intersection Theory, section 1.5; Gunning and Rossi, Analytic Functions of Several Complex Variables, chapter II.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_multiplicity_locally_constant_at_smooth_affine_point
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    [Smooth (ComplexPoint.openScheme X U).hom]
    (γ : AlgebraicCycle X.left ℚ) {r c : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e)
    (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom γ ↔ (e y).2 = 0)
    (x : ComplexPoint X) (hx : x ∈ e.source) (hxS : x ∈ a3b4_cycleSupport X.hom γ)
    (hxU : x.underlying ∈ U) :
    ∃ W : Opens (ComplexPoint X), (W : Set _) ⊆ e.source ∧ x ∈ W ∧
      ∀ y ∈ W, y ∈ a3b4_cycleSupport X.hom γ →
        a3b4_multiplicity X.hom γ y = a3b4_multiplicity X.hom γ x := by
  letI : Smooth (ComplexPoint.openScheme (Over.mk X.hom) U).hom := by
    change Smooth (U.ι ≫ X.hom)
    exact inferInstanceAs (Smooth (ComplexPoint.openScheme X U).hom)
  let P : Opens (ComplexPoint X) :=
    ⟨Point.underlying ⁻¹' (U : Set X.left),
      U.isOpen.preimage (ComplexPoint.continuous_underlying_to_zariski X)⟩
  let e' := e.restrOpen (P : Set (ComplexPoint X)) P.isOpen
  have he' : a3b4_IsHolChart X.hom e' :=
    a3b4g_isHolChart_restrOpen e he (P : Set (ComplexPoint X)) P.isOpen
  have hS' : ∀ y ∈ e'.source, y ∈ a3b4_cycleSupport X.hom γ ↔ (e' y).2 = 0 :=
    fun y hy => hS y hy.1
  obtain ⟨W, hWe, hxW, hmult⟩ :=
    properCycle_chart_multiplicity_locally_constant_on_smooth_affine_open X.hom U hU γ e' he'
      (fun y hy => hy.2) hS' x ⟨hx, hxU⟩ hxS
  exact ⟨W, fun y hy => (hWe hy).1, hxW, hmult⟩

end HodgeLean.Foundations.QuotientDuality

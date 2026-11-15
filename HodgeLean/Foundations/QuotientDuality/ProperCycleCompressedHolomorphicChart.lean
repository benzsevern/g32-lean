import HodgeLean.Foundations.QuotientDuality.ProperCycleHolomorphicLinearCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

/-! # Original compressed holomorphic product chart coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The original complex linear compression of a holomorphic product chart has holomorphic coordinates on its actual source.
Source: properCycle_holomorphic_linear_coordinates; a3b4_IsHolChart.
HC no distance; AV milestone no distance. -/
lemma properCycle_compressed_holomorphic_chart
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (r d : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin d → ℂ)))
    (he : a3b4_IsHolChart X.hom e) :
    let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r+d) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq
        (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
    let φ := e.trans L.toHomeomorph.toOpenPartialHomeomorph
    ∀ j, (f4_analytification X).IsHolFun (fun z : φ.source => φ z j) := by
  dsimp only
  let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r+d) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
  let φ := e.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hsub : φ.source ⊆ e.source := fun _ h => h.1
  have hf1 (j : Fin r) := anb_isHolFun_restrict (f4_analytification X).atlas hsub (he.1 j)
  have hf2 (j : Fin d) := anb_isHolFun_restrict (f4_analytification X).atlas hsub (he.2 j)
  exact properCycle_holomorphic_linear_coordinates (f4_analytification X) φ.source r d (r+d)
    (fun z => e z.val) ⟨hf1, hf2⟩ L.toContinuousLinearMap

end HodgeLean.Foundations.QuotientDuality

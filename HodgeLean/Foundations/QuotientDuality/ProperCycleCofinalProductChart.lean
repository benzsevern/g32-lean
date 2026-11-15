import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexStarChart
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-! # Cofinal restriction of actual normed-space product charts -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Radial compression gives an actual homeomorphism from a real normed vector space onto a positive-radius ball.
Source: Munkres, Topology, section 18, radial homeomorphisms of balls.
HC no distance; AV milestone no distance. -/
def properCycle_ball_coordinates (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) (r : ℝ) (hr : 0 < r) : E ≃ₜ Metric.ball c r :=
  (Homeomorph.Set.univ E).symm.trans
    ((Homeomorph.setCongr (OpenPartialHomeomorph.univBall_source c r).symm).trans
      ((OpenPartialHomeomorph.univBall c r).toHomeomorphSourceTarget.trans
        (Homeomorph.setCongr (OpenPartialHomeomorph.univBall_target c hr))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual marked product charts restrict cofinally while retaining a full normed tangential factor.
Source: Munkres, Topology, sections 18 and 19, product neighborhoods and radial ball coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_chart_cofinal
    (X : TopCat.{0}) (A : Set X) (U : Opens X)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (y : Y) (e : U ≃ₜ (E × Y))
    (hmark : ∀ w : U, (w : X) ∈ A ↔ (e w).2 = y)
    (x : U) (hxA : (x : X) ∈ A) (V : Opens X) (hxV : (x : X) ∈ V) :
    ∃ W : Opens X, W ≤ V ∧ (x : X) ∈ W ∧
      ∃ (Z : TopCat.{0}) (z : Z) (f : W ≃ₜ (E × Z)),
        ∀ w : W, (w : X) ∈ A ↔ (f w).2 = z := by
  let O : Set (E × Y) := e '' {w : U | (w : X) ∈ V}
  have hO : IsOpen O := e.isOpenMap _ (V.isOpen.preimage continuous_subtype_val)
  have hxO : e x ∈ O := ⟨x, hxV, rfl⟩
  obtain ⟨P, Q, hP, hQ, hxP, hxQ, hPQ⟩ :=
    isOpen_prod_iff.mp hO (e x).1 (e x).2 hxO
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hP (e x).1 hxP
  have hyQ : y ∈ Q := (hmark x).mp hxA ▸ hxQ
  let R : Opens U := ⟨e ⁻¹' (Metric.ball (e x).1 r ×ˢ Q),
    (Metric.isOpen_ball.prod hQ).preimage e.continuous⟩
  let W : Opens X := ⟨Subtype.val '' (R : Set U),
    U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ R.isOpen⟩
  have hWV : W ≤ V := by
    rintro w ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := hPQ ⟨hball ha.1, ha.2⟩
    exact e.injective hba ▸ hb
  have hxW : (x : X) ∈ W := ⟨x, ⟨Metric.mem_ball_self hr, hxQ⟩, rfl⟩
  let Z := TopCat.of Q
  let z : Z := ⟨y, hyQ⟩
  let f0 : R ≃ₜ W := U.isOpen.isOpenEmbedding_subtypeVal.isEmbedding.homeomorphImage (R : Set U)
  let f1 : R ≃ₜ (Metric.ball (e x).1 r ×ˢ Q) :=
    e.subtype (p := fun a => e a ∈ Metric.ball (e x).1 r ×ˢ Q)
      (q := fun b => b ∈ Metric.ball (e x).1 r ×ˢ Q) (fun _ => Iff.rfl)
  let f2 := Homeomorph.Set.prod (Metric.ball (e x).1 r) Q
  let f : W ≃ₜ (E × Z) :=
    ((f0.symm.trans f1).trans f2).trans
      ((properCycle_ball_coordinates E (e x).1 r hr).symm.prodCongr (Homeomorph.refl Q))
  refine ⟨W, hWV, hxW, Z, z, f, ?_⟩
  intro w
  have hval : (((f0.symm w).val : U) : X) = (w : X) :=
    congrArg (fun a : W => (a : X)) (f0.apply_symm_apply w)
  rw [Subtype.ext_iff]
  change (w : X) ∈ A ↔ (e (f0.symm w).val).2 = y
  exact hval ▸ hmark (f0.symm w).val

end HodgeLean.Foundations.QuotientDuality

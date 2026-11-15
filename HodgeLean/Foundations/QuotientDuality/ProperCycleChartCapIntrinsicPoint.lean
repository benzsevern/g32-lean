import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicFlatChartPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarGlobalChartNormalization

/-! # Actual global cap and intrinsic component point comparison
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_chartCapIntrinsicPoint_t2
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] : T2Space (ComplexPoint X) := f4_t2Space X

local instance properCycle_chartCapIntrinsicPoint_an_t2
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] : T2Space (a3b4_an X.hom) := f4_t2Space X

/-- The original supported normal multiplicity has actual global cap point value equal to the same multiplicity times the original common cap scalar and the specified intrinsic component point value.
Source: ProperCycleSupportCollar.global_chart_normalization; properCycle_intrinsic_flat_chart_point; properCycle_flat_support_point_pair_bijective.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_cap_intrinsic_point
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (ξ : X.left) (hξ : ξ ∈ γ.support)
    (r d : ℕ) (hdim : topologicalKrullDim (cycleComponent X.left ξ) = (r : ℕ))
    (C : ProperCycleSupportCollar (a3b4_an X.hom) (a3b4_cycleSupport X.hom γ))
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin d → ℂ)))
    (hflat : ∀ x ∈ e.source, x ∈ a3b4_cycleSupport X.hom γ ↔ (e x).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (O : Opens (TopCat.of (a3b4_cycleSupport X.hom γ)))
    (hOr : (O : Set (a3b4_cycleSupport X.hom γ)) ⊆
      Set.range (properCycle_component_support_map X γ ξ hξ))
    (hOe : ∀ s ∈ O, s.val ∈ e.source)
    (y : ComplexPoint (properCycle_component_over X ξ))
    (hy : properCycle_component_support_map X γ ξ hξ y ∈ O)
    (W : Opens (ComplexPoint X)) (hWe : (W : Set (ComplexPoint X)) ⊆ e.source)
    (hWN : (W : Set (ComplexPoint X)) ⊆ C.neighborhood)
    (hR : ∀ (x : ComplexPoint X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (hzW : (properCycle_component_support_map X γ ξ hξ y).val ∈ W)
    (hcenter : e (properCycle_component_support_map X γ ξ hξ y).val = (0, 0))
    (m : ℚ) (a : CohomologyWithSupport ℚ (a3b4_an X.hom) (a3b4_cycleSupport X.hom γ) (2*d))
    (ha : relativeCohomologyMap ℚ (2*d)
      (b6m_subspacePairMap (a3b4_an X.hom) (W : Set (ComplexPoint X)) (a3b4_cycleSupport X.hom γ)ᶜ) a =
      m • chartNormalProjectionCoclass (Fin r → ℂ) d e (a3b4_cycleSupport X.hom γ) hflat (W : Set (ComplexPoint X)) hWe)
    (c : Homology ℚ (a3b4_an X.hom) (2*d+2*r)) :
    let z := properCycle_component_support_map X γ ξ hξ y
    let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r+d) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq
        (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
    let φ := e.trans L.toHomeomorph.toOpenPartialHomeomorph
    let degree := eqToIso (congrArg (fun n => orientationGroup (a3b4_an X.hom) n z.val)
      (show 2*(r+d) = 2*d+2*r by omega))
    localOrientation (a3b4_an X.hom) (2*d+2*r) c z.val = degree.hom.hom
      (localClassOfChart (r+d) φ z.val ⟨hWe hzW, Set.mem_univ _⟩) →
    localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*r)
      (C.cap (a3b4a_classSupport_isClosed X.hom γ) (2*d) (2*r) c a) z =
      (m * properCycle_standard_complex_cap_scalar r d) •
        localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*r)
          (properCycle_intrinsic_component_on_support X γ ξ hξ r hdim) z := by
  dsimp only
  intro hc
  let z := properCycle_component_support_map X γ ξ hξ y
  let V : Opens (TopCat.of (a3b4_cycleSupport X.hom γ)) :=
    ⟨{s | s.val ∈ e.source}, e.open_source.preimage continuous_subtype_val⟩
  let o := properCycle_open_local_homology_iso (TopCat.of (a3b4_cycleSupport X.hom γ))
    V ⟨z, hWe hzW⟩ (2*r)
  let g := relativeHomologyMap ℚ (2*r)
    (properCycle_flat_support_point_pair (a3b4_an X.hom) (a3b4_cycleSupport X.hom γ)
      e 0 hflat z (hWe hzW) (congrArg Prod.fst hcenter))
  let F := g.comp o.inv.hom
  have hF : Function.Injective F :=
    (properCycle_flat_support_point_pair_bijective (a3b4_an X.hom)
      (a3b4_cycleSupport X.hom γ) e 0 hflat z (hWe hzW) (congrArg Prod.fst hcenter) (2*r)).1.comp
      o.toLinearEquiv.symm.injective
  have hG := C.global_chart_normalization (a3b4a_classSupport_isClosed X.hom γ)
    r d e W hWe hWN hR hflat z hzW hcenter m a ha c hc
  have hI := properCycle_intrinsic_flat_chart_point X γ ξ hξ r d hdim e hflat he O hOr hOe y hy hcenter
  apply hF
  rw [map_smul]
  change g (o.inv.hom _) = (m * properCycle_standard_complex_cap_scalar r d) • g (o.inv.hom _)
  rw [hG, hI]

end HodgeLean.Foundations.QuotientDuality

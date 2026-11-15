import HodgeLean.Foundations.QuotientDuality.ProperCycleFlatMultiplicityNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedFlatCapPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleScalarCollarNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleChartCapIntrinsicPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalCollarCap

/-! # Original normal restrictions from actual coordinates in centered charts
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace Topology
open HodgeLean.Adapters HodgeLean.Foundations.Analytic HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Literal actual cap coordinates give the original scalar supported normalization at every centered flattened chart point, including component intersection points.
Source: properCycle_flat_multiplicity_neighborhood; properCycle_connected_flat_cap_point; properCycle_chart_cap_intrinsic_point; properCycle_scalar_collar_neighborhood.
HC no distance; AV milestone no distance. -/
lemma properCycle_centered_coordinates_normalization
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k)) (a : s2e_supportedClass X γ k)
    (hcoords : properCycle_cap_coordinates X k hk hdim γ hc c a = fun ξ => γ ξ.val)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin k → ℂ) × (Fin k → ℂ)))
    (hflat : ∀ u ∈ e.source, u ∈ a3b4_cycleSupport X.hom γ ↔ (e u).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (x : ComplexPoint X) (hx : x ∈ e.source) (hxS : x ∈ a3b4_cycleSupport X.hom γ)
    (hcenter : e x = (0, 0)) :
    let L : ((Fin k → ℂ) × (Fin k → ℂ)) ≃L[ℂ] (Fin (k+k) → ℂ) :=
        ContinuousLinearEquiv.ofFinrankEq
          (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
    let φ := e.trans L.toHomeomorph.toOpenPartialHomeomorph
    let degree := eqToIso (congrArg (fun n => orientationGroup (a3b4_an X.hom) n x)
        (show 2*(k+k) = 2*k+2*k by omega))
    localOrientation (a3b4_an X.hom) (2*k+2*k) c x = degree.hom.hom
        (localClassOfChart (k+k) φ x ⟨hx, Set.mem_univ _⟩) →
    ∃ (W : Set (ComplexPoint X)) (hW : W ⊆ e.source), IsOpen W ∧ x ∈ W ∧
      relativeCohomologyMap ℚ (2*k) (a3b4_neighborhoodPairMap W (a3b4_cycleSupport X.hom γ)) a =
        a3b4_multiplicity X.hom γ x •
          chartNormalProjectionCoclass (Fin k → ℂ) k e (a3b4_cycleSupport X.hom γ) hflat W hW := by
  dsimp only
  intro hpoint
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : T2Space (a3b4_an X.hom) := f4_t2Space X
  let C := properCycle_original_support_collar X γ
  obtain ⟨j, ξ, hj, hj0, hje, hξ, hmult⟩ := properCycle_flat_multiplicity_neighborhood
    X k hk hdim γ hc k e hflat he ⟨x, hxS⟩ hx
  obtain ⟨y, hy⟩ := hξ 0
  let z := properCycle_component_support_map X γ ξ.val ξ.property y
  have hz : z = j 0 := hy
  have hzx : z.val = x := congrArg Subtype.val (hz.trans hj0)
  have hzval : (properCycle_component_support_map X γ ξ.val ξ.property y).val = x := hzx
  let O : Opens (TopCat.of (a3b4_cycleSupport X.hom γ)) := ⟨Set.range j, hj.isOpen_range⟩
  have hOr : (O : Set (a3b4_cycleSupport X.hom γ)) ⊆
      Set.range (properCycle_component_support_map X γ ξ.val ξ.property) := by
    rintro s ⟨u, rfl⟩; exact hξ u
  have hOe : ∀ s ∈ O, s.val ∈ e.source := by rintro s ⟨u, rfl⟩; exact hje u
  have hyO : z ∈ O := ⟨0, hz.symm⟩
  obtain ⟨W, hWe, hxW, hWN, hR, m, ha⟩ := properCycle_scalar_collar_neighborhood
    X γ k a C k e hflat x hx hxS
  have hzW : z.val ∈ W := hzx ▸ hxW
  have hcentery : e z.val = (0, 0) := hzx ▸ hcenter
  have hG := properCycle_chart_cap_intrinsic_point X γ ξ.val ξ.property k k
    (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property))
    C e hflat he O hOr hOe y hyO W hWe hWN hR hzW hcentery m a ha c (by
      dsimp only
      subst x
      exact hpoint)
  rw [properCycle_original_collar_cap] at hG
  have hV := properCycle_connected_flat_cap_point X k hk hdim γ hc k e hflat
    (TopCat.of (Fin k → ℂ)) j hj hje ξ hξ c a 0
  rw [← hz, hcoords] at hV
  have hI := properCycle_intrinsic_flat_chart_point X γ ξ.val ξ.property k k
    (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property))
    e hflat he O hOr hOe y hyO hcentery
  have hn : localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
      (properCycle_intrinsic_component_on_support X γ ξ.val ξ.property k
        (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property))) z ≠ 0 := by
    intro hzero
    dsimp only at hI
    rw [hzero, map_zero, map_zero] at hI
    exact standardComplexLocalClass_ne_zero_for_chart k hI.symm
  have hm : m = γ ξ.val := mul_right_cancel₀
    (properCycle_standard_complex_cap_scalar_ne_zero k k)
    (smul_left_injective ℚ hn (hG.symm.trans hV))
  have hmx : a3b4_multiplicity X.hom γ x = γ ξ.val := by
    have h := hmult 0
    rw [hj0] at h
    exact h
  refine ⟨W, hWe, W.isOpen, hxW, ?_⟩
  rw [hm, ← hmx] at ha
  exact ha

end HodgeLean.Foundations.QuotientDuality

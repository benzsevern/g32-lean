import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalizedCollarNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalProportionality

/-! # Actual scalar restrictions on original collar chart neighborhoods
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original supported class has an actual scalar normal restriction on a neighborhood satisfying the original collar chart and retraction requirements.
Source: a3b4a_classLocal_eq_smul_normalCoclass; ProperCycleSupportCollar.chart_neighborhood; properCycle_chart_normal_coclass_restrOpen.
HC no distance; AV milestone no distance. -/
lemma properCycle_scalar_collar_neighborhood
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ) (a : s2e_supportedClass X γ k)
    (C : ProperCycleSupportCollar (a3b4_an X.hom) (a3b4_cycleSupport X.hom γ))
    (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (hflat : ∀ u ∈ e.source, u ∈ a3b4_cycleSupport X.hom γ ↔ (e u).2 = 0)
    (x : ComplexPoint X) (hx : x ∈ e.source) (hxS : x ∈ a3b4_cycleSupport X.hom γ) :
    ∃ (W : Opens (ComplexPoint X)) (hWe : (W : Set (ComplexPoint X)) ⊆ e.source),
      x ∈ W ∧ ∃ hWN : (W : Set (ComplexPoint X)) ⊆ C.neighborhood,
      (∀ (u : ComplexPoint X) (hu : u ∈ W), (C.retraction ⟨u, hWN hu⟩).val ∈ e.source) ∧
      ∃ m : ℚ, relativeCohomologyMap ℚ (2*k)
        (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) (a3b4_cycleSupport X.hom γ)) a =
      m • chartNormalProjectionCoclass (Fin r → ℂ) k e (a3b4_cycleSupport X.hom γ)
        hflat (W : Set (ComplexPoint X)) hWe := by
  let S := a3b4_cycleSupport X.hom γ
  obtain ⟨O0, hxO, hOe, hON, hRO⟩ := C.chart_neighborhood e ⟨x, hxS⟩ hx
  let O : Opens (ComplexPoint X) := ⟨O0.carrier, O0.isOpen⟩
  let e' := e.restrOpen (O : Set (ComplexPoint X)) O.isOpen
  have hx' : x ∈ e'.source := ⟨hx, hxO⟩
  have hflat' : ∀ u ∈ e'.source, u ∈ S ↔ (e' u).2 = 0 := fun u hu => hflat u hu.1
  let W := flattenedSupportNeighborhood (Fin r → ℂ) k e' x hx'
  have hWe' : (W : Set (ComplexPoint X)) ⊆ e'.source :=
    flattenedSupportNeighborhood_subset_source (Fin r → ℂ) k e' x hx'
  have hWe : (W : Set (ComplexPoint X)) ⊆ e.source := fun u hu => (hWe' hu).1
  have hWO : (W : Set (ComplexPoint X)) ⊆ O := fun u hu => (hWe' hu).2
  let aW := relativeCohomologyMap ℚ (2*k) (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) S) a
  let m := relativeCohomologyEquivDualHomology ℚ _ (2*k) aW
    (flattenedSupportNormalClass (Fin r → ℂ) k e' x hx' S hflat' ((hflat' x hx').mp hxS))
  have hscalar := a3b4a_classLocal_eq_smul_normalCoclass e' S hflat' x hx' hxS aW m rfl
  rw [properCycle_chart_normal_coclass_restrOpen k e S hflat O W hWe'] at hscalar
  refine ⟨W, hWe, mem_flattenedSupportNeighborhood (Fin r → ℂ) k e' x hx',
    fun u hu => hON (hWO hu), ?_, m, hscalar⟩
  intro u hu
  exact hRO u (hWO hu)

end HodgeLean.Foundations.QuotientDuality

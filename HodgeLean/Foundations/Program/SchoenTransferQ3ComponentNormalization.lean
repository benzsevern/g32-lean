import HodgeLean.Adapters.NormalConeB4aClassHolomorphicCharts
import HodgeLean.Adapters.KleimanProductChartClass

/-! Local holomorphic readings of the canonical supported component class. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology Filter
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- An analytic expression in the specified algebraic chart has a
neighbourhood satisfying the original holomorphic-coordinate predicate. -/
theorem s4_q3_holomorphic_restriction_of_chart_analytic
    (X : Over (Spec ↧ℂ)) (d r c : ℕ) [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (x : ComplexPoint X) (hx : x ∈ e.source)
    (he : AnalyticAt ℂ ((localChart X d x).symm.trans e) (localChart X d x x)) :
    ∃ (V : Set (ComplexPoint X)) (hV : IsOpen V), x ∈ V ∧
      a3b4_IsHolChart X.hom (e.restrOpen V hV) := by
  let χ := localChart X d x
  have hxχ := mem_localChart_source X d x
  have hχ : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω χ x :=
    (contMDiffOn_chart (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) (x := x)).contMDiffAt
      (χ.open_source.mem_nhds hxχ)
  have htrans : ContMDiffAt 𝓘(ℂ, Fin d → ℂ)
      𝓘(ℂ, (Fin r → ℂ) × (Fin c → ℂ)) ω (χ.symm.trans e) (χ x) :=
    he.contDiffAt.contMDiffAt
  have hreg : ContMDiffAt 𝓘(ℂ, Fin d → ℂ)
      𝓘(ℂ, (Fin r → ℂ) × (Fin c → ℂ)) ω e x := by
    apply (htrans.comp x hχ).congr_of_eventuallyEq
    filter_upwards [χ.open_source.mem_nhds hxχ] with y hy
    change e y = e (χ.symm (χ y))
    rw [χ.left_inv hy]
  exact a3b4a_classLocal_exists_holomorphic_restriction X d r c e x hx hreg


/-- The canonical sheaf component class has its actual singular comparison
normalized in a holomorphic support chart near every smooth support point. -/
theorem s4_q3_component_class_holomorphic_chart
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (k : ℕ) (p : X.left) (hp : Order.coheight p = k)
    (x : ComplexPoint X) (hx : x ∈ cycleComponentSmoothSupportAmbientOpen X p)
    (hxS : x ∈ cycleComponentSupport X p) :
    ∃ (e : OpenPartialHomeomorph (ComplexPoint X)
        ((Fin (dim X.left - k) → ℂ) × (Fin k → ℂ)))
      (hflat : ∀ y ∈ e.source, y ∈ cycleComponentSupport X p ↔ (e y).2 = 0),
      x ∈ e.source ∧ a3b4_IsHolChart X.hom e ∧
      ∃ (V : Opens (ComplexPoint X)) (_ : x ∈ V) (hVe : (V : Set (ComplexPoint X)) ⊆ e.source),
        relativeCohomologyMap ℚ (2 * k)
          (neighborhoodSupportInclusionPairMap (Set.subset_univ _) (cycleComponentSupport X p))
          (supportedSingularClass X (cycleComponentAnalyticClosedSupport X p) (2 * k)
            (cycleComponentSupportedInjectiveClass X p hp)) =
        chartNormalProjectionCoclass (Fin (dim X.left - k) → ℂ) k e
          (cycleComponentSupport X p) hflat V hVe := by
  obtain ⟨e, hflat, hxe, hA, hI, W, hxW, hWe, hW⟩ :=
    hc9k_cc_componentClass_restrict_normalChart X k p hp x hx hxS
  obtain ⟨O, hO, hxO, hhol⟩ :=
    s4_q3_holomorphic_restriction_of_chart_analytic X (dim X.left) (dim X.left - k) k e x hxe hA
  let e' := e.restrOpen O hO
  have hflat' : ∀ y ∈ e'.source, y ∈ cycleComponentSupport X p ↔ (e' y).2 = 0 :=
    fun y hy => hflat y hy.1
  let V : Opens (ComplexPoint X) := W ⊓ ⟨O, hO⟩
  have hVe : (V : Set (ComplexPoint X)) ⊆ e'.source := fun y hy => ⟨hWe hy.1, hy.2⟩
  refine ⟨e', hflat', ⟨hxe, hxO⟩, hhol, V, ⟨hxW, hxO⟩, hVe, ?_⟩
  have hh := congrArg (relativeCohomologyMap ℚ (2 * k)
    (neighborhoodSupportInclusionPairMap (show V ≤ W from inf_le_left)
      (cycleComponentSupport X p))) hW
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp] at hh
  rw [chartNormalProjectionCoclass_restrict] at hh
  exact hh

end HodgeLean.Foundations.Program

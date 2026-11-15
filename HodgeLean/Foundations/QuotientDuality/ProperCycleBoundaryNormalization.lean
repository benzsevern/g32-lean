import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalModelDetection
import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicCodimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalization
import HodgeLean.Foundations.QuotientDuality.ProperCycleTopology

/-! # Original complex normalization recovered across smaller algebraic boundaries -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Exact chart-model germs off an algebraic boundary recover the original normalization at every chart point, including points on that boundary.
Source: Fulton, Intersection Theory, section 19.1; Bredon, Sheaf Theory, second edition, II.10 and V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_normalized_of_off_boundary_chart_models
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2 * k)
    (hvan : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    (γ : AlgebraicCycle X.left ℚ)
    (hcodim : ∀ ξ ∈ γ.support, (k : ℕ∞) ≤ Order.coheight ξ)
    (B : Closeds X.left) (hBS : B ≤ a3b4a_classAlgebraicSupport X.hom γ)
    (hgeneric : ∀ ξ ∈ γ.support, ξ ∉ B) (a : s2e_supportedClass X γ k)
    (hmodels : ∀ (r : ℕ)
      (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
      (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom γ ↔ (e y).2 = 0)
      (x : ComplexPoint X), x ∈ e.source → x ∈ a3b4_cycleSupport X.hom γ →
      a3b4_IsHolChart X.hom e →
      ∃ (V : Opens (ComplexPoint X)), x ∈ V ∧ ∃ hVe : (V : Set (ComplexPoint X)) ⊆ e.source,
        ∀ (y : ComplexPoint X) (hy : y ∈ V), y.underlying ∉ B →
          supportRelativeCohomologyGerm (a3b4_an X.hom) (a3b4_cycleSupport X.hom γ) (2 * k) V y hy
            (relativeCohomologyMap ℚ (2 * k)
              (a3b4_neighborhoodPairMap (V : Set (ComplexPoint X)) (a3b4_cycleSupport X.hom γ)) a) =
          supportRelativeCohomologyGerm (a3b4_an X.hom) (a3b4_cycleSupport X.hom γ) (2 * k) V y hy
            (a3b4_multiplicity X.hom γ x • chartNormalProjectionCoclass (Fin r → ℂ) k e
              (a3b4_cycleSupport X.hom γ) hS (V : Set (ComplexPoint X)) hVe)) :
    a3b4_IsCycleClass X.hom γ k a := by
  letI : LocallyOfFiniteType X.hom := inferInstance
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI (V : Opens (ComplexPoint X)) : ParacompactSpace V := properCycle_open_paracompact X V
  have hSdim := properCycle_closed_support_dimension_le_of_coheight X
    (a3b4a_classAlgebraicSupport X.hom γ) k
    (a3b4a_classAlgebraicSupport_coheight X.hom γ k hcodim)
  rw [hdim, show 2 * k - k = k by omega] at hSdim
  have hBdim := properCycle_closed_support_dimension_le_of_coheight X B (k + 1)
    (a3b4a_classAlgebraicSupport_boundary_coheight X.hom γ k hcodim B hBS hgeneric)
  rw [hdim, show 2 * k - (k + 1) = k - 1 by omega] at hBdim
  intro r e hS x hx hxS he
  obtain ⟨V, hxV, hVe, hV⟩ := hmodels r e hS x hx hxS he
  refine ⟨(V : Set (ComplexPoint X)), hVe, V.isOpen, hxV, ?_⟩
  exact properCycle_relative_eq_of_off_boundary_germs X
    (a3b4a_classAlgebraicSupport X.hom γ) B hBS k (k - 1) hSdim hBdim
    (2 * (2 * k)) hvan (2 * k) (by omega) (by omega) V _ _ hV

end HodgeLean.Foundations.QuotientDuality

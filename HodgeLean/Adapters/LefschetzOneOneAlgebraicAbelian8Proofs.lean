import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8Defs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian16
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian13Endpoint

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open Set Topology
namespace HodgeLean.Adapters

/-- Removing the critical zeros of a reduced analytic equation does not lose a degree-two
supported cohomology class.
Source: Bredon, *Sheaf Theory*, second edition, Chapter V, local cohomology and supports;
Gunning--Rossi, Chapter III, the singular locus of a reduced hypersurface. -/
theorem bh8_singular_restriction_aux (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p)) :
    Function.Injective (relativeCohomologyMap ℚ 2 (bh8_regularInclusion n f)) := by
  exact bh16_singular_restriction n f hf hred

/-- On the regular-domain pair, a reduced equation has the normalized component coclass.
Source: Griffiths--Harris, Chapter 1, section 1, the local divisor class;
`cycleComponentSupportedInjectiveClass_normalization`. -/
theorem bh8_regular_normalization_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hs : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x) :
    relativeCohomologyMap ℚ 2 (bh8_regularInclusion (dim X.left) f)
      (relativeCohomologyMap ℚ 2 (bh8_coverMap X x f hs)
        (complexSupportInjectiveSectionCohomologyEquiv X
          (cycleComponentAnalyticClosedSupport X x) ⊤ 2
          ((rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) 2)
            (cycleComponentSupportedInjectiveClass X x hx)))) =
    relativeCohomologyMap ℚ 2 (bh8_regularInclusion (dim X.left) f)
      (relativeCohomologyMap ℚ 2 (bh8_normalMap (dim X.left) f
        (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt))
        (normalizedPointCoclass 1)) := by
  exact bh13_regular_normalization X x hx f hf hred hs

set_option maxHeartbeats 400000 in
/-- Pullback along the period square, with exactly the stage-five supported-pullback type.
Source: regular normalization, injective singular restriction, and functoriality of pairs. -/
theorem bh8_supported_pullback_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hsupport : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0)
    (ha : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      abelianExp X (bh4_squareEdge X l m z i t) ∉ cycleComponentSupport X x) :
    relativeCohomologyMap ℚ 2 (bh5_componentPairMap X x l m z ha)
      (complexSupportInjectiveSectionCohomologyEquiv X
        (cycleComponentAnalyticClosedSupport X x) ⊤ 2
        ((rationalSupportAddEquivSupportedInjectiveHomology X
          (cycleComponentAnalyticClosedSupport X x) 2)
          (cycleComponentSupportedInjectiveClass X x hx))) =
    relativeCohomologyMap ℚ 2
      (bh5_equationPairMap X l m z f
        (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt) hnz)
      (normalizedPointCoclass 1) := by
  have h := bh8_singular_restriction_aux (dim X.left) f hf hred
    (bh8_regular_normalization_aux X x hx f hf hred hsupport)
  have h' := congrArg (relativeCohomologyMap ℚ 2
    (bh8_diskToEquation X f l m z hnz)) h
  have hc : bh5_componentPairMap X x l m z ha =
      bh8_diskToEquation X f l m z hnz ≫ bh8_coverMap X x f hsupport := by rfl
  have he : bh5_equationPairMap X l m z f
      (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt) hnz =
      bh8_diskToEquation X f l m z hnz ≫ bh8_normalMap (dim X.left) f
        (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt) := by rfl
  rw [hc, he, relativeCohomologyMap_comp, relativeCohomologyMap_comp]
  exact h'

end HodgeLean.Adapters

import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian6DegreeProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8OrientationProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8Proofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian11Orientation
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5SquareMaps

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open Set Topology
namespace HodgeLean.Adapters

/-- Pullback of the normalized component class equals pullback of the normal-line coclass.
This includes extension across the singular locus; it contains no winding integral.
Source: Griffiths--Harris, Chapter 1, section 1, the local divisor class;
`cycleComponentSupportedInjectiveClass_normalization`. -/
theorem bh5_supported_pullback_aux
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
  exact bh8_supported_pullback_aux X x hx f hf hred hsupport l m z hnz ha

/-- The disk orientation agrees with the ordered period-pair evaluation.
Source: Hatcher, section 3.3, relative evaluation and naturality;
Birkenhake--Lange, section 1.3, exterior description of torus cohomology. -/
theorem bh5_square_orientation_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (hx : Order.coheight x = 1)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (ha : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      abelianExp X (bh4_squareEdge X l m z i t) ∉ cycleComponentSupport X x) :
    bh4_periodPair X l m
      (forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) 2
        (cycleComponentSupportedInjectiveClass X x hx)) =
    relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
      (relativeCohomologyMap ℚ 2 (bh5_componentPairMap X x l m z ha)
        (complexSupportInjectiveSectionCohomologyEquiv X
          (cycleComponentAnalyticClosedSupport X x) ⊤ 2
          ((rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) 2)
            (cycleComponentSupportedInjectiveClass X x hx)))) bh5_diskClass := by
  exact (bh8_period_coefficient_aux X l m z _).trans
    (bh11_square_torus X x (cycleComponentSupportedInjectiveClass X x hx) l m z ha)

/-- Relative evaluation of the normal-line coclass is the logarithmic boundary integral.
The real period square need not be a holomorphic disk and its interior zeros need not be isolated.
Source: Ahlfors, *Complex Analysis*, Chapter 4, section 5, argument principle;
Hatcher, section 2.2, degree and its relative-homology interpretation. -/
theorem bh5_argument_principle_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    (relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
      (relativeCohomologyMap ℚ 2
        (bh5_equationPairMap X l m z f
          (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt) hnz)
        (normalizedPointCoclass 1)) bh5_diskClass : ℂ) =
      bh4_boundaryWinding X l m z f := by
  exact bh6_argument_principle X f hf l m z hnz

/-- Composition with exactly the stage-four supported-square-evaluation target.
Source: relative pullback, oriented evaluation, and the argument principle above. -/
theorem bh5_supported_square_evaluation_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hsupport : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    (bh4_periodPair X l m
      (forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) 2
        (cycleComponentSupportedInjectiveClass X x hx)) : ℂ) =
      bh4_boundaryWinding X l m z f := by
  have ha : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      abelianExp X (bh4_squareEdge X l m z i t) ∉ cycleComponentSupport X x := by
    intro i t ht hs
    exact hnz i t ht ((hsupport _).mpr hs)
  rw [bh5_square_orientation_aux X x hx l m z ha,
    bh5_supported_pullback_aux X x hx f hf hred hsupport l m z hnz ha]
  exact bh5_argument_principle_aux X f hf l m z hnz

end HodgeLean.Adapters

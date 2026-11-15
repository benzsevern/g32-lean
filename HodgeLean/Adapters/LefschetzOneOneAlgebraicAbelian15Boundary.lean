import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian15BoundaryProofs
/-! # Algebraic boundary covers

Implication from the actual component coheight to a codimension-two cover of
its singular boundary upstairs. Component smooth dimensions are obtained from
the existing algebraic dimension theorem, before countable chart assembly.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open TopologicalSpace Set Filter Topology
open scoped Manifold ContDiff CategoryTheory.MonObj
open HodgeLean.RealDefs
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

/-- The smooth part of an algebraic component has countably many charts of its actual complex dimension.
Source: `cycleComponentSmoothLocus_smoothOfRelativeDimension`, complex manifold charts,
and second countability of the locally closed analytic support. -/
theorem bh15_component_smooth_cover (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (q : ℕ) (hx : Order.coheight x = q) :
    ∃ (U : ℕ → Set (Fin (dim X.left - q) → ℂ))
      (g : ℕ → (Fin (dim X.left - q) → ℂ) → ComplexPoint X),
      (∀ j, IsOpen (U j)) ∧
      (∀ j, ContMDiffOn 𝓘(ℂ, Fin (dim X.left - q) → ℂ)
        𝓘(ℂ, Fin (dim X.left) → ℂ) ω (g j) (U j)) ∧
      cycleComponentSmoothSupport X x = ⋃ j, g j '' U j :=
  bh15_component_smooth_cover_aux X x q hx

/-- An algebraic coheight bound transfers to the parameter dimensions of a countable manifold-valued cover.
This is the algebraic-to-analytic intermediate used for the singular boundary.
Source: `bh15_component_smooth_cover`, Noetherian induction as in
`ccm5_closed_supportH_subsingleton_of_coheight`, and the component dimension formula. -/
theorem bh15_algebraic_coheight_cover (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds X.left) (q : ℕ)
    (hc : ∀ z ∈ S, (q : ℕ∞) ≤ Order.coheight z) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → ComplexPoint X),
      (∀ j, (U j).Nonempty → d j + q ≤ dim X.left) ∧
      (∀ j, IsOpen (U j)) ∧
      (∀ j, ContMDiffOn 𝓘(ℂ, Fin (d j) → ℂ)
        𝓘(ℂ, Fin (dim X.left) → ℂ) ω (g j) (U j)) ∧
      (Point.underlying : ComplexPoint X → X.left) ⁻¹' (S : Set X.left) =
        ⋃ j, g j '' U j :=
  bh15_algebraic_coheight_cover_aux X S q hc

/-- The exponential preimage of a prime divisor singular boundary has a countable codimension-two cover.
Source: `ccm5_singularBoundary_coheight_lower_bound`, `bh15_algebraic_coheight_cover`,
`spec_complexExponential_localBiholomorph`, and `bh15_lift_cover`. -/
theorem bh15_boundary_stratification (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (hx : Order.coheight x = 1) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → (Fin (dim X.left) → ℂ)),
      (∀ j, (U j).Nonempty → d j + 2 ≤ dim X.left) ∧
      (∀ j, IsOpen (U j)) ∧
      (∀ j, DifferentiableOn ℂ (g j) (U j)) ∧
      abelianExp X ⁻¹'
        (cycleComponentSingularAnalyticClosedFiltration X x 0 :
          Set (ComplexPoint X)) = ⋃ j, g j '' U j :=
  bh15_boundary_stratification_aux X x hx

/-- Critical zeros together with the exponential singular boundary have a countable codimension-two cover.
Source: `bh15_critical_stratification`, `bh15_boundary_stratification`, and `bh15_union_cover`. -/
theorem bh15_critical_boundary_stratification (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p)) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → (Fin (dim X.left) → ℂ)),
      (∀ j, (U j).Nonempty → d j + 2 ≤ dim X.left) ∧
      (∀ j, IsOpen (U j)) ∧
      (∀ j, DifferentiableOn ℂ (g j) (U j)) ∧
      ({p | f p = 0 ∧ fderiv ℂ f p = 0} ∪
        abelianExp X ⁻¹' (cycleComponentSingularAnalyticClosedFiltration X x 0 :
          Set (ComplexPoint X))) = ⋃ j, g j '' U j :=
  bh15_critical_boundary_stratification_aux X x hx f hf hred

end HodgeLean.Adapters

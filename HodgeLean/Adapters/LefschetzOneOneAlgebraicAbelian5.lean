import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5AnalyticProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5AvoidanceProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5EvaluationProofs

/-! # Stage five: intermediate analytic and topological interfaces

An implication from the separately stated projectivity, analytic-dimension,
principalization, relative-pullback and evaluation obligations. The five final statements
have exactly the stage-four target types. Their bodies are compositions; the eight
primitive analytic and geometric statements remain open. No new geometric predicate
or tagged hypothesis is introduced. See the companion document for infrastructure gaps,
estimates, and the distinction between constructed and conditional examples.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open Set Filter Topology Metric
namespace HodgeLean.Adapters

/-- A nowhere-zero section trivializes the integral alternating form.
Source: `spec_chernForm_coboundary` and `spec_chernForm_datumOfX`. -/
theorem spec_bh5_nowhere_zero_form
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (hnz : ∀ z, θ z ≠ 0) : A.E = 0 :=
  bh5_nowhere_zero_form_aux X A θ hθ hnz

example
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (hnz : ∀ z, θ z ≠ 0) : A.E = 0 :=
  spec_bh5_nowhere_zero_form X A θ hθ hnz

/-- Positivity in positive dimension forces a nonzero integral form.
Source: `spec_hermitian_eq_of_imaginary_lattice`; Birkenhake--Lange, Lemma 1.3.1. -/
theorem spec_bh5_positive_form_ne_zero
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite)
    (hdim : 0 < dim X.left) : A.E ≠ 0 :=
  bh5_positive_form_ne_zero_aux X A hpos hdim

example
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite)
    (hdim : 0 < dim X.left) : A.E ≠ 0 :=
  spec_bh5_positive_form_ne_zero X A hpos hdim

/-- Composition through the integral form, with exactly the stage-four theta target.
Source: Birkenhake--Lange, section 3.1; the preceding two lemmas. -/
theorem spec_bh5_theta_zero
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite)
    (hdim : 0 < dim X.left) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) :
    ∃ z, θ z = 0 :=
  bh5_theta_zero_aux X A hpos hdim θ hθ

example
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite)
    (hdim : 0 < dim X.left) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) :
    ∃ z, θ z = 0 :=
  spec_bh5_theta_zero X A hpos hdim θ hθ

/-- Reduced local equations with the same zero germ differ by a unit.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
local analytic Nullstellensatz and unique factorization. -/
theorem spec_bh5_reduced_associated (n : ℕ) (p : Fin n → ℂ)
    (f g : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hfr : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p))
    (hgr : Squarefree (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p))
    (hz : ∀ᶠ z in 𝓝 p, f z = 0 ↔ g z = 0) : AreAssociatedAt f g p :=
  bh5_reduced_associated_aux n p f g hf hg hfr hgr hz

example (n : ℕ) (p : Fin n → ℂ)
    (f g : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hfr : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p))
    (hgr : Squarefree (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p))
    (hz : ∀ᶠ z in 𝓝 p, f z = 0 ↔ g z = 0) : AreAssociatedAt f g p :=
  spec_bh5_reduced_associated n p f g hf hg hfr hgr hz

/-- A locally reduced hypersurface on affine complex space has a reduced entire equation.
Source: Gunning--Rossi, Chapter VIII, Cousin II on a contractible Stein space;
local analytic unique factorization. -/
theorem spec_bh5_reduced_principalization (n : ℕ) (S : Set (Fin n → ℂ))
    (hloc : ∀ p, ∃ (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p),
      Squarefree (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p) ∧
      ∀ᶠ z in 𝓝 p, g z = 0 ↔ z ∈ S) :
    ∃ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ),
      (∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
        AnalyticGermAt n p)) ∧ (∀ p, f p = 0 ↔ p ∈ S) :=
  bh5_reduced_principalization_aux n S hloc

example (n : ℕ) (S : Set (Fin n → ℂ))
    (hloc : ∀ p, ∃ (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p),
      Squarefree (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p) ∧
      ∀ᶠ z in 𝓝 p, g z = 0 ↔ z ∈ S) :
    ∃ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ),
      (∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
        AnalyticGermAt n p)) ∧ (∀ p, f p = 0 ↔ p ∈ S) :=
  spec_bh5_reduced_principalization n S hloc

/-- Composition with exactly the stage-four reduced-cover-equations target.
Source: Cousin II on complex affine space and the local multiplicity field of algebraization. -/
theorem spec_bh5_reduced_cover_equations
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (D : bh4_LocalDivisorData X) (R : bh4_Algebraization X D) :
    ∃ f : Fin R.n → (Fin (dim X.left) → ℂ) → ℂ,
      ∃ hf : ∀ i, AnalyticOnNhd ℂ (f i) univ,
        (∀ i p, Squarefree (⟨Filter.Germ.ofFun (f i), f i, hf i p (mem_univ p), rfl⟩ :
          AnalyticGermAt (dim X.left) p)) ∧
        (∀ i p, f i p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X (R.x i)) ∧
        (∀ j p, p ∈ D.V j →
          AreAssociatedAt (D.f j) (fun z ↦ ∏ i, f i z ^ R.mult i) p) :=
  bh5_reduced_cover_equations_aux X D R

example
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (D : bh4_LocalDivisorData X) (R : bh4_Algebraization X D) :
    ∃ f : Fin R.n → (Fin (dim X.left) → ℂ) → ℂ,
      ∃ hf : ∀ i, AnalyticOnNhd ℂ (f i) univ,
        (∀ i p, Squarefree (⟨Filter.Germ.ofFun (f i), f i, hf i p (mem_univ p), rfl⟩ :
          AnalyticGermAt (dim X.left) p)) ∧
        (∀ i p, f i p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X (R.x i)) ∧
        (∀ j p, p ∈ D.V j →
          AreAssociatedAt (D.f j) (fun z ↦ ∏ i, f i z ^ R.mult i) p) :=
  spec_bh5_reduced_cover_equations X D R

/-- The projectivity bridge, before Hermitian reconstruction and semicharacters.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, second edition, section 4.3,
Riemann's projectivity criterion. -/
theorem spec_bh5_projective_riemann_form
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    ∃ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l, E l l = 0) ∧ (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧ (∀ v, v ≠ 0 → 0 < B v (Complex.I • v)) :=
  bh5_projective_riemann_form_aux X

example
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    ∃ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l, E l l = 0) ∧ (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧ (∀ v, v ≠ 0 → 0 < B v (Complex.I • v)) :=
  spec_bh5_projective_riemann_form X

/-- Reconstruct the positive datum from the projective Riemann form.
Source: `spec_exists_datumOfX_of_riemann`; Birkenhake--Lange, Lemma 1.3.1. -/
theorem spec_bh5_polarization
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : ∃ A₀ : bh4_AHData X, A₀.H.IsPositiveDefinite :=
  bh5_polarization_aux X

example
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : ∃ A₀ : bh4_AHData X, A₀.H.IsPositiveDefinite :=
  spec_bh5_polarization X

/-- A proper analytic subset of positive-dimensional complex affine space has real
Hausdorff dimension at most twice the complex dimension minus two.
Source: Gunning--Rossi, Chapter III, dimension and regular loci of analytic sets. -/
theorem spec_bh5_analytic_dim (n : ℕ) (hn : 0 < n) (Z : Set (Fin n → ℂ))
    (hZ : IsClosedAnalytic (Fin n → ℂ) Z) (hp : Z ≠ univ) :
    dimH Z ≤ (2 * n - 2 : ℕ) :=
  bh5_analytic_dim_aux n hn Z hZ hp

example (n : ℕ) (hn : 0 < n) (Z : Set (Fin n → ℂ))
    (hZ : IsClosedAnalytic (Fin n → ℂ) Z) (hp : Z ≠ univ) :
    dimH Z ≤ (2 * n - 2 : ℕ) :=
  spec_bh5_analytic_dim n hn Z hZ hp

/-- Sweeping by one compact real segment increases Hausdorff dimension by at most one.
Source: Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Chapter 8,
product with an interval and Lipschitz images. -/
theorem spec_bh5_segment_dim (n : ℕ) (Z : Set (Fin n → ℂ)) (a v : Fin n → ℂ) :
    dimH (bh5_segmentIncidence n Z a v) ≤ dimH Z + 1 :=
  bh5_segment_dim_aux n Z a v

example (n : ℕ) (Z : Set (Fin n → ℂ)) (a v : Fin n → ℂ) :
    dimH (bh5_segmentIncidence n Z a v) ≤ dimH Z + 1 :=
  spec_bh5_segment_dim n Z a v

/-- The four affine boundary edges avoid a proper analytic set after one translation.
Source: analytic-set dimension, compact segment dimension growth, and finite-union dimension. -/
theorem spec_bh5_analytic_set_avoidance
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (Z : Set (Fin (dim X.left) → ℂ))
    (hZ : IsClosedAnalytic (Fin (dim X.left) → ℂ) Z) (hproper : Z ≠ univ)
    (l m : abelianPeriodLattice X) :
    ∃ z : Fin (dim X.left) → ℂ, ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      bh4_squareEdge X l m z i t ∉ Z :=
  bh5_analytic_set_avoidance_aux X Z hZ hproper l m

example
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (Z : Set (Fin (dim X.left) → ℂ))
    (hZ : IsClosedAnalytic (Fin (dim X.left) → ℂ) Z) (hproper : Z ≠ univ)
    (l m : abelianPeriodLattice X) :
    ∃ z : Fin (dim X.left) → ℂ, ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      bh4_squareEdge X l m z i t ∉ Z :=
  spec_bh5_analytic_set_avoidance X Z hZ hproper l m

/-- Pullback of the normalized component class equals pullback of the normal-line coclass.
This includes extension across the singular locus; it contains no winding integral.
Source: Griffiths--Harris, Chapter 1, section 1, the local divisor class;
`cycleComponentSupportedInjectiveClass_normalization`. -/
theorem spec_bh5_supported_pullback
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
      (normalizedPointCoclass 1) :=
  bh5_supported_pullback_aux X x hx f hf hred hsupport l m z hnz ha

example
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
      (normalizedPointCoclass 1) :=
  spec_bh5_supported_pullback X x hx f hf hred hsupport l m z hnz ha

/-- The disk orientation agrees with the ordered period-pair evaluation.
Source: Hatcher, section 3.3, relative evaluation and naturality;
Birkenhake--Lange, section 1.3, exterior description of torus cohomology. -/
theorem spec_bh5_square_orientation
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
            (cycleComponentSupportedInjectiveClass X x hx)))) bh5_diskClass :=
  bh5_square_orientation_aux X x hx l m z ha

example
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
            (cycleComponentSupportedInjectiveClass X x hx)))) bh5_diskClass :=
  spec_bh5_square_orientation X x hx l m z ha

/-- Relative evaluation of the normal-line coclass is the logarithmic boundary integral.
The real period square need not be a holomorphic disk and its interior zeros need not be isolated.
Source: Ahlfors, *Complex Analysis*, Chapter 4, section 5, argument principle;
Hatcher, section 2.2, degree and its relative-homology interpretation. -/
theorem spec_bh5_argument_principle
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
      bh4_boundaryWinding X l m z f :=
  bh5_argument_principle_aux X f hf l m z hnz

example
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
      bh4_boundaryWinding X l m z f :=
  spec_bh5_argument_principle X f hf l m z hnz

/-- Composition with exactly the stage-four supported-square-evaluation target.
Source: relative pullback, oriented evaluation, and the argument principle above. -/
theorem spec_bh5_supported_square_evaluation
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
      bh4_boundaryWinding X l m z f :=
  bh5_supported_square_evaluation_aux X x hx f hf hred hsupport l m z hnz

example
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
      bh4_boundaryWinding X l m z f :=
  spec_bh5_supported_square_evaluation X x hx f hf hred hsupport l m z hnz

end HodgeLean.Adapters

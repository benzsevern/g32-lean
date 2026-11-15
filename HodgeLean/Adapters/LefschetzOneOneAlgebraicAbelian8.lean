import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8Proofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8OrientationProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8CurvatureProofs

/-! # Algebraic Appell--Humbert stage eight: review draft

These are implications from projective local lifts, from a reduced analytic equation,
and from explicit boundary avoidance. Three composed endpoints have the exact stage-five
types. The arbitrary-projective endpoint starts with the original geometric instances.
The eight primitive analytic and topological obligations remain open.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AppellHumbert HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open Set Topology
open scoped ContDiff
namespace HodgeLean.Adapters

/-- Removing the critical zeros of a reduced analytic equation does not lose a degree-two
supported cohomology class.
Source: Bredon, *Sheaf Theory*, second edition, Chapter V, local cohomology and supports;
Gunning--Rossi, Chapter III, the singular locus of a reduced hypersurface. -/
theorem bh8_singular_restriction (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p)) :
    Function.Injective (relativeCohomologyMap ℚ 2 (bh8_regularInclusion n f)) :=
  bh8_singular_restriction_aux n f hf hred

example (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p)) :
    Function.Injective (relativeCohomologyMap ℚ 2 (bh8_regularInclusion n f)) :=
  bh8_singular_restriction n f hf hred

/-- On the regular-domain pair, a reduced equation has the normalized component coclass.
Source: Griffiths--Harris, Chapter 1, section 1, the local divisor class;
`cycleComponentSupportedInjectiveClass_normalization`. -/
theorem bh8_regular_normalization
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
        (normalizedPointCoclass 1)) :=
  bh8_regular_normalization_aux X x hx f hf hred hs

example
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
        (normalizedPointCoclass 1)) :=
  bh8_regular_normalization X x hx f hf hred hs

/-- Pullback along the period square, with exactly the stage-five supported-pullback type.
Source: regular normalization, injective singular restriction, and functoriality of pairs. -/
theorem bh8_supported_pullback
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
  bh8_supported_pullback_aux X x hx f hf hred hsupport l m z hnz ha

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
  bh8_supported_pullback X x hx f hf hred hsupport l m z hnz ha

/-- The increasing-coordinate coefficient of the period torus is the exterior period pairing.
Source: Birkenhake--Lange, second edition, section 1.3;
`abelianPeriod` and naturality of the cup-wedge comparison. -/
theorem bh8_period_coefficient
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (c : HQ X 2) :
    bh4_periodPair X l m c = bh8_torusCoefficient
      (cohomologyMap ℚ 2 (TopCat.ofHom (bh8_periodTorus X l m z)) (cupComparison X 2 c)) :=
  bh8_period_coefficient_aux X l m z c

example
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (c : HQ X 2) :
    bh4_periodPair X l m c = bh8_torusCoefficient
      (cohomologyMap ℚ 2 (TopCat.ofHom (bh8_periodTorus X l m z)) (cupComparison X 2 c)) :=
  bh8_period_coefficient X l m z c

/-- Local homogeneous lifts of a projective embedding give a periodic projective immersion
of the abelian universal cover.
Source: Griffiths--Harris, Chapter 0, projective embeddings and analytic coordinates;
Birkenhake--Lange, second edition, section 4.3. -/
theorem bh8_projective_atlas
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : Nonempty (bh8_ProjectiveAtlas (dim X.left) (abelianPeriodLattice X)) :=
  bh8_projective_atlas_aux X

example
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : Nonempty (bh8_ProjectiveAtlas (dim X.left) (abelianPeriodLattice X)) :=
  bh8_projective_atlas X

/-- Normalized Fubini--Study curvature glues smoothly, is closed and periodic, and is positive
of type (1,1) on a projective immersion.
Source: Griffiths--Harris, Chapter 0, Hermitian differential geometry and the Fubini--Study metric. -/
theorem bh8_curvature_geometry (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) :
    ContDiff ℝ ∞ (bh8_curvature n Λ A) ∧
    (∀ (l : Λ) p, bh8_curvature n Λ A (p + l) = bh8_curvature n Λ A p) ∧
    (∀ p v, bh8_curvature n Λ A p v v = 0) ∧
    (∀ p, IsTypeOneOne (fun v w ↦ bh8_curvature n Λ A p v w)) ∧
    (∀ p v, v ≠ 0 → 0 < bh8_curvature n Λ A p v (Complex.I • v)) ∧
    (∀ p u v w,
      fderiv ℝ (bh8_curvature n Λ A) p u v w +
      fderiv ℝ (bh8_curvature n Λ A) p v w u +
      fderiv ℝ (bh8_curvature n Λ A) p w u v = 0) :=
  bh8_curvature_geometry_aux n Λ A

example (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) :
    ContDiff ℝ ∞ (bh8_curvature n Λ A) ∧
    (∀ (l : Λ) p, bh8_curvature n Λ A (p + l) = bh8_curvature n Λ A p) ∧
    (∀ p v, bh8_curvature n Λ A p v v = 0) ∧
    (∀ p, IsTypeOneOne (fun v w ↦ bh8_curvature n Λ A p v w)) ∧
    (∀ p v, v ≠ 0 → 0 < bh8_curvature n Λ A p v (Complex.I • v)) ∧
    (∀ p u v w,
      fderiv ℝ (bh8_curvature n Λ A) p u v w +
      fderiv ℝ (bh8_curvature n Λ A) p v w u +
      fderiv ℝ (bh8_curvature n Λ A) p w u v = 0) :=
  bh8_curvature_geometry n Λ A

/-- The normalized curvature has integral periods on every lattice parallelogram.
The integer comes from the transition functions of O(1), before translation averaging.
Source: Griffiths--Harris, Chapter 1, section 1, first Chern class and curvature;
Birkenhake--Lange, section 2.1, integral alternating forms. -/
theorem bh8_chern_periods (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (z : Fin n → ℂ) (l m : Λ) :
    ∃ k : ℤ, bh8_surfacePeriod n (bh8_curvature n Λ A) z l m = k :=
  bh8_chern_periods_aux n Λ A z l m

example (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (z : Fin n → ℂ) (l m : Λ) :
    ∃ k : ℤ, bh8_surfacePeriod n (bh8_curvature n Λ A) z l m = k :=
  bh8_chern_periods n Λ A z l m

/-- Translation averaging preserves periods, type and strict positivity of a closed form.
Source: Birkenhake--Lange, section 4.3, invariant positive integral forms on a complex torus;
Stokes' theorem applied to translated period parallelograms. -/
theorem bh8_averaging (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin (2 * n)) ℤ Λ)
    (form : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) (hperiodic : ∀ (l : Λ) p, form (p + l) = form p)
    (halt : ∀ p v, form p v v = 0)
    (h11 : ∀ p, IsTypeOneOne (fun v w ↦ form p v w))
    (hpos : ∀ p v, v ≠ 0 → 0 < form p v (Complex.I • v))
    (hclosed : ∀ p u v w,
      fderiv ℝ form p u v w + fderiv ℝ form p v w u + fderiv ℝ form p w u v = 0) :
    (∀ l m : Λ, bh8_average n Λ b form l m = bh8_surfacePeriod n form 0 l m) ∧
    (∀ v, bh8_average n Λ b form v v = 0) ∧
    IsTypeOneOne (fun v w ↦ bh8_average n Λ b form v w) ∧
    (∀ v, v ≠ 0 → 0 < bh8_average n Λ b form v (Complex.I • v)) :=
  bh8_averaging_aux n Λ b form hform hperiodic halt h11 hpos hclosed

example (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin (2 * n)) ℤ Λ)
    (form : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) (hperiodic : ∀ (l : Λ) p, form (p + l) = form p)
    (halt : ∀ p v, form p v v = 0)
    (h11 : ∀ p, IsTypeOneOne (fun v w ↦ form p v w))
    (hpos : ∀ p v, v ≠ 0 → 0 < form p v (Complex.I • v))
    (hclosed : ∀ p u v w,
      fderiv ℝ form p u v w + fderiv ℝ form p v w u + fderiv ℝ form p w u v = 0) :
    (∀ l m : Λ, bh8_average n Λ b form l m = bh8_surfacePeriod n form 0 l m) ∧
    (∀ v, bh8_average n Λ b form v v = 0) ∧
    IsTypeOneOne (fun v w ↦ bh8_average n Λ b form v w) ∧
    (∀ v, v ≠ 0 → 0 < bh8_average n Λ b form v (Complex.I • v)) :=
  bh8_averaging n Λ b form hform hperiodic halt h11 hpos hclosed

/-- Exact stage-five projective Riemann-form endpoint, through curvature, Chern periods and averaging.
Source: Birkenhake--Lange, second edition, section 4.3, Riemann's projectivity criterion. -/
theorem bh8_projective_riemann_form
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    ∃ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l, E l l = 0) ∧ (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧ (∀ v, v ≠ 0 → 0 < B v (Complex.I • v)) :=
  bh8_projective_riemann_form_aux X

example
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    ∃ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l, E l l = 0) ∧ (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧ (∀ v, v ≠ 0 → 0 < B v (Complex.I • v)) :=
  bh8_projective_riemann_form X

/-- Positive Appell--Humbert data on the projective abelian variety.
Source: `spec_exists_datumOfX_of_riemann`; Birkenhake--Lange, Lemma 1.3.1 and Theorem 2.2.3. -/
theorem bh8_polarization
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : ∃ A₀ : bh4_AHData X, A₀.H.IsPositiveDefinite :=
  bh8_polarization_aux X

example
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : ∃ A₀ : bh4_AHData X, A₀.H.IsPositiveDefinite :=
  bh8_polarization X

end HodgeLean.Adapters

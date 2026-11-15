import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelianProofs

/-! # Algebraic Appell--Humbert interface

This stage gives the analytic-divisor/GAGA work an exact target and proves the remaining formal
passage to scoped Lefschetz `(1,1)` as an implication from the open geometric auxiliaries.
The GAGA interface itself is an explicit untagged binder with no cohomological fields.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass
open Filter Set Topology
open scoped MonoidalCategory

open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

omit [GrpObj X] in
/-- A codimension-one algebraic component contributes its fundamental class to the algebraic
cycle-class span.
Source: `AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan`. -/
theorem spec_bh4_cycleComponentSheafClass_mem_span (x : X.left)
    (hx : Order.coheight x = 1) :
    cycleComponentSheafClass X x hx ∈ algebraicCycleClassSpan X 1 :=
  bh4_cycleComponentSheafClass_mem_span X x hx

/-- Nonzero theta sections of positive data, using the existing theta-existence theorem.
Source: Birkenhake--Lange, second edition, section 3.1; `spec_sections_ne_bot`. -/
theorem spec_bh4_theta_nonzero (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite) :
    ∃ θ : (Fin (dim X.left) → ℂ) → ℂ,
      θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter) ∧ θ ≠ 0 :=
  bh4_theta_nonzero_aux X A hpos

/-- The theta functional equation uses the holomorphic automorphy factor.
Source: Birkenhake--Lange, second edition, section 3.1; `AppellHumbert.sections`. -/
theorem spec_bh4_theta_periodicity (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (l : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ) :
    θ (z + l) = holFactor (datumOfX X A.H A.E A.integral A.chi A.semicharacter) l z * θ z :=
  bh4_theta_periodicity_aux X A θ hθ l z

omit [GrpObj X] [Smooth X.hom] [IsProjective X.hom] in
/-- A nonzero entire function has a nonzero germ at every point of the connected cover.
Source: Gunning--Rossi, Chapter I, identity theorem; `AnalyticOnNhd.eq_of_eventuallyEq`. -/
theorem spec_bh4_theta_nonzero_germ
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : θ ≠ 0)
    (p : Fin (dim X.left) → ℂ) : ¬ ∀ᶠ z in nhds p, θ z = 0 :=
  bh4_theta_nonzero_germ_aux X θ hθ hne p

/-- The nonvanishing automorphy factor associates the translated theta equation.
Source: Birkenhake--Lange, second edition, section 3.1; `holFactor_ne_zero`. -/
theorem spec_bh4_theta_translation_associated (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (l : abelianPeriodLattice X) (p : Fin (dim X.left) → ℂ) :
    AreAssociatedAt θ (fun z ↦ θ (z + l)) p :=
  bh4_theta_translation_associated_aux X A θ hθ l p

/-- One global equation gives valid invariant local divisor data with the specified support.
Source: Griffiths--Harris, Chapter 1, section 1; `IsLocalDivisorData`. -/
theorem spec_bh4_theta_local_data
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : Differentiable ℂ θ)
    (hgerm : ∀ p, ¬ ∀ᶠ z in nhds p, θ z = 0)
    (htrans : ∀ (l : abelianPeriodLattice X) p,
      AreAssociatedAt θ (fun z ↦ θ (z + l)) p) :
    ∃ D : bh4_LocalDivisorData X,
      (∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p) ∧
      localDivisorSupport D.V D.f = {z | θ z = 0} ∧
      abelianExp X '' localDivisorSupport D.V D.f = thetaZeroLocusX X θ :=
  bh4_theta_local_data_aux X θ hθ hgerm htrans

/-- Projectivity supplies positive integral Hermitian data on the fixed period lattice.
Source: Birkenhake--Lange, second edition, sections 4.3 and 2.2. -/
theorem spec_bh4_polarization : ∃ A₀ : bh4_AHData X, A₀.H.IsPositiveDefinite :=
  bh4_polarization_aux X

/-- A sufficiently large positive integral multiple dominates an arbitrary Hermitian form.
Source: Birkenhake--Lange, second edition, section 4.3; compactness of the unit sphere. -/
theorem spec_bh4_domination (H H₀ : HermitianForm (V := Fin (dim X.left) → ℂ))
    (hpos : H₀.IsPositiveDefinite) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ v : Fin (dim X.left) → ℂ, v ≠ 0 →
      0 < (H.toFun v v).re + (n : ℝ) * (H₀.toFun v v).re :=
  bh4_domination_aux X H H₀ hpos

/-- Products and powers of semicharacters realize the integral sum and multiple of forms.
Source: Birkenhake--Lange, second edition, Theorem 2.2.3. -/
theorem spec_bh4_semicharacter_assembly (A A₀ : bh4_AHData X) (n : ℕ) :
    ∃ P M : bh4_AHData X,
      (∀ v w, P.H.toFun v w = A.H.toFun v w + (n : ℂ) * A₀.H.toFun v w) ∧
      (∀ v w, M.H.toFun v w = (n : ℂ) * A₀.H.toFun v w) ∧
      P.E = A.E + n • A₀.E ∧ M.E = n • A₀.E ∧
      (∀ l, P.chi l = A.chi l * A₀.chi l ^ n) ∧
      (∀ l, M.chi l = A₀.chi l ^ n) :=
  bh4_semicharacter_assembly_aux X A A₀ n

/-- Positive data in positive dimension cannot have a nowhere-vanishing theta section.
Source: Birkenhake--Lange, second edition, section 3.1 (theta divisors). -/
theorem spec_bh4_theta_zero (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite)
    (hdim : 0 < dim X.left) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) :
    ∃ z, θ z = 0 :=
  bh4_theta_zero_aux X A hpos hdim θ hθ

example (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite)
    (hdim : 0 < dim X.left) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) :
    ∃ z, θ z = 0 := spec_bh4_theta_zero X A hpos hdim θ hθ

/-- Positive Appell--Humbert data have a nonzero section and its effective divisor on the cover.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, second edition, section 3.1;
Griffiths--Harris, Chapter 1, section 1. -/
theorem spec_bh4_theta_divisor (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite) :
    ∃ θ : (Fin (dim X.left) → ℂ) → ℂ,
      θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter) ∧ θ ≠ 0 ∧
      ∃ D : bh4_LocalDivisorData X,
        (∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p) ∧
        localDivisorSupport D.V D.f = {z | θ z = 0} ∧
        abelianExp X '' localDivisorSupport D.V D.f = thetaZeroLocusX X θ ∧
        (0 < dim X.left → Set.Nonempty (localDivisorSupport D.V D.f)) :=
  bh4_theta_divisor_aux X A hpos

example (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite) :
    ∃ θ : (Fin (dim X.left) → ℂ) → ℂ,
      θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter) ∧ θ ≠ 0 ∧
      ∃ D : bh4_LocalDivisorData X,
        (∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p) ∧
        localDivisorSupport D.V D.f = {z | θ z = 0} ∧
        abelianExp X '' localDivisorSupport D.V D.f = thetaZeroLocusX X θ ∧
        (0 < dim X.left → Set.Nonempty (localDivisorSupport D.V D.f)) := spec_bh4_theta_divisor X A hpos

-- Positive-dimensional family: projectivity supplies the polarization; the support is nonempty.
-- This example uses the open polarization and theta-zero obligations.
example (hdim : 0 < dim X.left) :
    ∃ A : bh4_AHData X, A.H.IsPositiveDefinite ∧
      ∃ θ : (Fin (dim X.left) → ℂ) → ℂ,
        θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter) ∧ θ ≠ 0 ∧
        ∃ D : bh4_LocalDivisorData X,
          localDivisorSupport D.V D.f = {z | θ z = 0} ∧
          Set.Nonempty (localDivisorSupport D.V D.f) := by
  obtain ⟨A, hpos⟩ := spec_bh4_polarization X
  obtain ⟨θ, hθ, hne, D, _, hs, _, hnonempty⟩ := spec_bh4_theta_divisor X A hpos
  exact ⟨A, hpos, θ, hθ, hne, D, hs, hnonempty hdim⟩

/-- Every Appell--Humbert class is a difference of two positive ones. Projectivity supplies
an integral positive polarization, a sufficiently large multiple of which dominates the given form.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, second edition, sections 2.2 and 4.3. -/
theorem spec_bh4_positive_difference (A : bh4_AHData X) :
    ∃ P M : bh4_AHData X, P.H.IsPositiveDefinite ∧ M.H.IsPositiveDefinite ∧
      latticeClassHQ X (-A.E) = latticeClassHQ X (-P.E) - latticeClassHQ X (-M.E) :=
  bh4_positive_difference_aux X A

example (A : bh4_AHData X) :
    ∃ P M : bh4_AHData X, P.H.IsPositiveDefinite ∧ M.H.IsPositiveDefinite ∧
      latticeClassHQ X (-A.E) = latticeClassHQ X (-P.E) - latticeClassHQ X (-M.E) := spec_bh4_positive_difference X A

/-- Ordered period-pair evaluations detect a rational degree-two class.
Source: Birkenhake--Lange, second edition, section 1.3; exterior duality. -/
theorem spec_bh4_periodPair_ext (c d : HQ X 2)
    (h : ∀ l m : abelianPeriodLattice X, bh4_periodPair X l m c = bh4_periodPair X l m d) :
    c = d :=
  bh4_periodPair_ext_aux X c d h

/-- An integral Hermitian form evaluates on the ordered period pair with coefficient one.
Source: Birkenhake--Lange, second edition, section 1.3; `latticeClassHQ`. -/
theorem spec_bh4_periodPair_lattice (A : bh4_AHData X) (l m : abelianPeriodLattice X) :
    bh4_periodPair X l m (latticeClassHQ X A.E) = (A.E l m : ℚ) :=
  bh4_periodPair_lattice_aux X A l m

/-- A proper closed analytic subset can be avoided by all four edges of a translated square.
Source: Gunning--Rossi, Chapter III, dimension of analytic sets and regular loci. -/
theorem spec_bh4_analytic_set_avoidance
    (Z : Set (Fin (dim X.left) → ℂ))
    (hZ : IsClosedAnalytic (Fin (dim X.left) → ℂ) Z) (hproper : Z ≠ univ)
    (l m : abelianPeriodLattice X) :
    ∃ z : Fin (dim X.left) → ℂ, ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      bh4_squareEdge X l m z i t ∉ Z :=
  bh4_analytic_set_avoidance_aux X Z hZ hproper l m

example
    (Z : Set (Fin (dim X.left) → ℂ))
    (hZ : IsClosedAnalytic (Fin (dim X.left) → ℂ) Z) (hproper : Z ≠ univ)
    (l m : abelianPeriodLattice X) :
    ∃ z : Fin (dim X.left) → ℂ, ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      bh4_squareEdge X l m z i t ∉ Z :=
  spec_bh4_analytic_set_avoidance X Z hZ hproper l m

/-- Opposite edges have compatible endpoint increments; integral lift constants cancel.
Source: Birkenhake--Lange, second edition, section 2.1 and Theorem 2.1.2. -/
theorem spec_bh4_opposite_edge_increments (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    let f := holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)
    ((g 0 1 - g 0 0) + (g 2 1 - g 2 0) = f m z - f m (z + l)) ∧
    ((g 1 1 - g 1 0) + (g 3 1 - g 3 0) = f l (z + m) - f l z) :=
  bh4_opposite_edge_increments_aux X A θ hθ l m z g hg hexp

example (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    let f := holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)
    ((g 0 1 - g 0 0) + (g 2 1 - g 2 0) = f m z - f m (z + l)) ∧
    ((g 1 1 - g 1 0) + (g 3 1 - g 3 0) = f l (z + m) - f l z) :=
  spec_bh4_opposite_edge_increments X A θ hθ l m z g hg hexp

/-- Reduced component divisors on the vector-space cover have entire equations. Their powered
product is locally associated to the given divisor.
Source: Gunning--Rossi, Chapter VIII, Cousin II on Stein manifolds; contractibility of complex affine space. -/
theorem spec_bh4_reduced_cover_equations (D : bh4_LocalDivisorData X)
    (R : bh4_Algebraization X D) :
    ∃ f : Fin R.n → (Fin (dim X.left) → ℂ) → ℂ,
      ∃ hf : ∀ i, AnalyticOnNhd ℂ (f i) univ,
        (∀ i p, Squarefree (⟨Filter.Germ.ofFun (f i), f i, hf i p (mem_univ p), rfl⟩ :
          AnalyticGermAt (dim X.left) p)) ∧
        (∀ i p, f i p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X (R.x i)) ∧
        (∀ j p, p ∈ D.V j →
          AreAssociatedAt (D.f j) (fun z ↦ ∏ i, f i z ^ R.mult i) p) :=
  bh4_reduced_cover_equations_aux X D R

example (D : bh4_LocalDivisorData X)
    (R : bh4_Algebraization X D) :
    ∃ f : Fin R.n → (Fin (dim X.left) → ℂ) → ℂ,
      ∃ hf : ∀ i, AnalyticOnNhd ℂ (f i) univ,
        (∀ i p, Squarefree (⟨Filter.Germ.ofFun (f i), f i, hf i p (mem_univ p), rfl⟩ :
          AnalyticGermAt (dim X.left) p)) ∧
        (∀ i p, f i p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X (R.x i)) ∧
        (∀ j p, p ∈ D.V j →
          AreAssociatedAt (D.f j) (fun z ↦ ∏ i, f i z ^ R.mult i) p) :=
  spec_bh4_reduced_cover_equations X D R

/-- Pullback of one reduced component to the period square evaluates its supported class
as the logarithmic-derivative integral along the boundary, with complex orientation.
Source: Griffiths--Harris, Chapter 1, section 1 (divisor class); Hatcher, section 3.3 (local orientations). -/
theorem spec_bh4_supported_square_evaluation (x : X.left) (hx : Order.coheight x = 1)
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
  bh4_supported_square_evaluation_aux X x hx f hf hred hsupport l m z hnz

example (x : X.left) (hx : Order.coheight x = 1)
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
  spec_bh4_supported_square_evaluation X x hx f hf hred hsupport l m z hnz

/-- Everywhere associated entire functions have the same boundary winding.
Source: Ahlfors, third edition, Chapter 4, section 5 (argument principle). -/
theorem spec_bh4_winding_association
    (f h : (Fin (dim X.left) → ℂ) → ℂ)
    (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (hassoc : ∀ p, AreAssociatedAt f h p)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    bh4_boundaryWinding X l m z f = bh4_boundaryWinding X l m z h :=
  bh4_winding_association_aux X f h hf hh hassoc l m z hnz

example
    (f h : (Fin (dim X.left) → ℂ) → ℂ)
    (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (hassoc : ∀ p, AreAssociatedAt f h p)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    bh4_boundaryWinding X l m z f = bh4_boundaryWinding X l m z h :=
  spec_bh4_winding_association X f h hf hh hassoc l m z hnz

/-- The winding of a product of powered equations is the multiplicity-weighted sum.
Source: Ahlfors, third edition, Chapter 4, section 5 (logarithmic derivative). -/
theorem spec_bh4_winding_multiplicities (n : ℕ)
    (f : Fin n → (Fin (dim X.left) → ℂ) → ℂ)
    (hf : ∀ j, Differentiable ℂ (f j)) (mult : Fin n → ℕ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ j i, ∀ t ∈ Icc (0 : ℝ) 1, f j (bh4_squareEdge X l m z i t) ≠ 0) :
    bh4_boundaryWinding X l m z (fun p ↦ ∏ j, f j p ^ mult j) =
      ∑ j, (mult j : ℂ) * bh4_boundaryWinding X l m z (f j) :=
  bh4_winding_multiplicities_aux X n f hf mult l m z hnz

example (n : ℕ)
    (f : Fin n → (Fin (dim X.left) → ℂ) → ℂ)
    (hf : ∀ j, Differentiable ℂ (f j)) (mult : Fin n → ℕ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ j i, ∀ t ∈ Icc (0 : ℝ) 1, f j (bh4_squareEdge X l m z i t) ≠ 0) :
    bh4_boundaryWinding X l m z (fun p ↦ ∏ j, f j p ^ mult j) =
      ∑ j, (mult j : ℂ) * bh4_boundaryWinding X l m z (f j) :=
  spec_bh4_winding_multiplicities X n f hf mult l m z hnz

/-- The oriented edges l, m, -l, -m and normalization by 2 pi i give the positive
sum of endpoint increments of the normalized logarithms.
Source: Ahlfors, third edition, Chapter 4, section 5; Hatcher, section 1.3. -/
theorem spec_bh4_winding_orientation
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      f (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    bh4_boundaryWinding X l m z f = bh4_boundaryIncrement g :=
  bh4_winding_orientation_aux X f hf l m z g hg hexp

example
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      f (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    bh4_boundaryWinding X l m z f = bh4_boundaryIncrement g :=
  spec_bh4_winding_orientation X f hf l m z g hg hexp

/-- A translate of the period square has no theta zeros along any of its four boundary edges.
Source: Gunning--Rossi, Chapter I (zero sets of nonzero holomorphic functions);
real dimension of an analytic hypersurface and its one-parameter translates. -/
theorem spec_bh4_boundary_avoiding
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : θ ≠ 0)
    (l m : abelianPeriodLattice X) :
    ∃ z : Fin (dim X.left) → ℂ, ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      θ (bh4_squareEdge X l m z i t) ≠ 0 :=
  bh4_boundary_avoiding_aux X θ hθ hne l m

/-- Each nonvanishing boundary edge has a continuous normalized logarithm lift on the interval.
Source: Hatcher, *Algebraic Topology*, section 1.3 (lifting to a covering space). -/
theorem spec_bh4_boundary_logs
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : Continuous θ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, θ (bh4_squareEdge X l m z i t) ≠ 0) :
    ∃ g : Fin 4 → ℝ → ℂ,
      (∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1)) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) 1 →
        θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :=
  bh4_boundary_logs_aux X θ hθ l m z hnz

/-- The sum of boundary logarithm increments is the negative Appell--Humbert Chern cocycle.
Source: Birkenhake--Lange, second edition, section 2.1 and Theorem 2.1.2. -/
theorem spec_bh4_boundary_chern (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    bh4_boundaryIncrement g =
      -(chernForm (holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) l m : ℂ) :=
  bh4_boundary_chern_aux X A θ hθ l m z g hg hexp

/-- The period of the normalized divisor fundamental class is its boundary winding increment.
Local association and reduced component equations specify the zero multiplicities.
Source: Griffiths--Harris, Chapter 1, section 1 (divisors and local fundamental classes);
Hatcher, section 3.3 (local orientations and duality). -/
theorem spec_bh4_boundary_fundamental
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : θ ≠ 0)
    (D : bh4_LocalDivisorData X)
    (hlocal : ∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p)
    (R : bh4_Algebraization X D)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    (bh4_periodPair X l m
      (∑ i, (R.mult i : ℚ) •
        forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X (R.x i)) 2
          (cycleComponentSupportedInjectiveClass X (R.x i) (R.codim i))) : ℂ) =
      bh4_boundaryIncrement g :=
  bh4_boundary_fundamental_aux X θ hθ hne D hlocal R l m z g hg hexp

/-- The theta divisor period is the negative logarithmic Chern cocycle on an ordered lattice pair.
The local equations and reduced component germs retain the multiplicities in this comparison.
Source: Griffiths--Harris, Chapter 1, section 1 (divisor and Chern correspondence);
Birkenhake--Lange, second edition, Theorem 2.1.2. -/
theorem spec_bh4_theta_divisor_period (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (hne : θ ≠ 0) (D : bh4_LocalDivisorData X)
    (hlocal : ∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p)
    (R : bh4_Algebraization X D) (l m : abelianPeriodLattice X) :
    bh4_periodPair X l m
      (∑ i, (R.mult i : ℚ) •
        forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X (R.x i)) 2
          (cycleComponentSupportedInjectiveClass X (R.x i) (R.codim i))) =
      -(chernForm (holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) l m : ℚ) :=
  bh4_theta_divisor_period_aux X A θ hθ hne D hlocal R l m

/-- The logarithmic Chern form represents the negative integral Hermitian form in rational cohomology.
Source: `spec_chernForm_datumOfX`; `latticeClassHQ`. -/
theorem spec_bh4_chern_normalization (A : bh4_AHData X)
    (E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE' : ∀ l m, E' l m = chernForm
      (holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) l m) :
    latticeClassHQ X E' = latticeClassHQ X (-A.E) :=
  bh4_chern_normalization_aux X A E' hE'

/-- Forgetting support transports the multiplicity-weighted normalized fundamental classes into
the algebraic cycle-class span.
Source: `cycleComponentSupportedInjectiveClass`; `cycleComponentSheafClass`;
`algebraicCycleClassSpan`. -/
theorem spec_bh4_fundamental_sum_mem_span (D : bh4_LocalDivisorData X)
    (R : bh4_Algebraization X D) :
    (∑ i, (R.mult i : ℚ) •
      forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X (R.x i)) 2
        (cycleComponentSupportedInjectiveClass X (R.x i) (R.codim i))) ∈
      algebraicCycleClassSpan X 1 :=
  bh4_fundamental_sum_mem_span_aux X D R

/-- The Chern form equals the signed fundamental class of an algebraized theta divisor.
The minus sign follows the repository convention `chernForm = -E`; the effective divisor has
class `E`. Local association, rather than just equality of supports, retains multiplicities.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Chapter 1, section 1;
`spec_chernForm_datumOfX`. -/
theorem spec_bh4_chern_comparison (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (hne : θ ≠ 0) (D : bh4_LocalDivisorData X)
    (hlocal : ∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p)
    (R : bh4_Algebraization X D) :
    latticeClassHQ X (-A.E) =
      -∑ i, (R.mult i : ℚ) • cycleComponentSheafClass X (R.x i) (R.codim i) :=
  bh4_chern_comparison_aux X A θ hθ hne D hlocal R

example (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (hne : θ ≠ 0) (D : bh4_LocalDivisorData X)
    (hlocal : ∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p)
    (R : bh4_Algebraization X D) :
    latticeClassHQ X (-A.E) =
      -∑ i, (R.mult i : ℚ) • cycleComponentSheafClass X (R.x i) (R.codim i) := spec_bh4_chern_comparison X A θ hθ hne D hlocal R

/-- Implication from geometric effective-divisor algebraization, via theta divisors, positive
reduction, and the Chern comparison. The existing Betti comparison inputs are retained.
Source: `spec_lefschetzOneOneFor_iff_appellHumbert_chernClassHQ`. -/
theorem spec_bh4_lefschetzOneOneFor_of_localDivisorDataAlgebraizes
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (hG : bh4_LocalDivisorDataAlgebraizes X) : LefschetzOneOneFor X :=
  bh4_lefschetzOneOneFor_of_localDivisorDataAlgebraizes X hF hBdR hG

example (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (hG : bh4_LocalDivisorDataAlgebraizes X) : LefschetzOneOneFor X :=
  spec_bh4_lefschetzOneOneFor_of_localDivisorDataAlgebraizes X hF hBdR hG

example (x : X.left) (hx : Order.coheight x = 1) :
    cycleComponentSheafClass X x hx ∈ algebraicCycleClassSpan X 1 :=
  spec_bh4_cycleComponentSheafClass_mem_span X x hx

example (hg : dim X.left = 0) : LefschetzOneOneFor X :=
  spec_lefschetzOneOneFor_dim_zero X hg

-- This curve conclusion uses no effective-divisor algebraization assumption.
example [SmoothOfRelativeDimension 1 X.hom] : LefschetzOneOneFor X := by
  unfold LefschetzOneOneFor
  rw [j5d_algebraicCycleClassSpan_one_eq_top complexPointsPreconnected X]
  exact le_top

example : (0 : HQ X 2) ∈ algebraicCycleClassSpan X 1 := Submodule.zero_mem _

-- For any algebraized component, reduced equations and an avoiding square supply the
-- single-component evaluation premises; no class comparison is used to obtain them.
example (D : bh4_LocalDivisorData X) (R : bh4_Algebraization X D) (j : Fin R.n)
    (l m : abelianPeriodLattice X) :
    ∃ f : (Fin (dim X.left) → ℂ) → ℂ, ∃ hf : AnalyticOnNhd ℂ f univ,
      (∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
        AnalyticGermAt (dim X.left) p)) ∧
      (∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X (R.x j)) ∧
      ∃ z : Fin (dim X.left) → ℂ, ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
        f (bh4_squareEdge X l m z i t) ≠ 0 := by
  obtain ⟨f, hf, hred, hs, _⟩ := spec_bh4_reduced_cover_equations X D R
  have hne : f j ≠ 0 := by
    intro he
    exact (hred j 0).ne_zero (Subtype.ext (congrArg Filter.Germ.ofFun he))
  obtain ⟨z, hnz⟩ := spec_bh4_boundary_avoiding X (f j)
    (fun p ↦ (hf j p (mem_univ p)).differentiableAt) hne l m
  exact ⟨f j, hf j, hred j, hs j, z, hnz⟩

-- An abelian curve specializes the positive-dimensional theta example.
example [SmoothOfRelativeDimension 1 X.hom] :
    ∃ A : bh4_AHData X, A.H.IsPositiveDefinite ∧
      ∃ D : bh4_LocalDivisorData X, Set.Nonempty (localDivisorSupport D.V D.f) := by
  have hdim : 0 < dim X.left := by rw [SmoothOfRelativeDimension.dim_eq X.hom 1]; omega
  obtain ⟨A, hpos⟩ := spec_bh4_polarization X
  obtain ⟨_, _, _, D, _, _, _, hn⟩ := spec_bh4_theta_divisor X A hpos
  exact ⟨A, hpos, D, hn hdim⟩

-- The empty analytic subset satisfies the properness premise, in every dimension.
example : ∃ Z : Set (Fin (dim X.left) → ℂ),
    IsClosedAnalytic (Fin (dim X.left) → ℂ) Z ∧ Z ≠ univ :=
  ⟨∅, isClosedAnalytic_empty, Set.empty_ne_univ⟩

-- The association-invariance premises have an entire unit witness.
example : ∃ f h : (Fin (dim X.left) → ℂ) → ℂ,
    Differentiable ℂ f ∧ Differentiable ℂ h ∧
      (∀ p, AreAssociatedAt f h p) ∧ (∀ p, f p ≠ 0) := by
  refine ⟨fun _ ↦ 1, fun _ ↦ 1, differentiable_const 1, differentiable_const 1, ?_,
    fun _ ↦ one_ne_zero⟩
  intro p
  exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
    Eventually.of_forall fun _ ↦ (one_mul _).symm⟩

-- Multiplicity weights are unrestricted; unit factors give genuine nonvanishing inputs.
example (n : ℕ) : ∃ f : Fin n → (Fin (dim X.left) → ℂ) → ℂ,
    (∀ j, Differentiable ℂ (f j)) ∧ (∀ j p, f j p ≠ 0) :=
  ⟨fun _ _ ↦ 1, fun _ ↦ differentiable_const 1, fun _ _ ↦ one_ne_zero⟩

-- Degenerate positivity check: on a zero-dimensional cover the zero form is positive.
example (hg : dim X.left = 0) : ∃ A : bh4_AHData X, A.H.IsPositiveDefinite := by
  obtain ⟨A, _, _, _⟩ := bh4_trivial_theta_witness X
  refine ⟨A, ?_⟩
  intro v hv
  have : IsEmpty (Fin (dim X.left)) := by rw [hg]; infer_instance
  exact (hv (Subsingleton.elim v 0)).elim

-- Periodicity and translation association both have the constant unit as a section witness.
example : ∃ A : bh4_AHData X,
    (fun _ ↦ (1 : ℂ)) ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter) := by
  obtain ⟨A, _, hθ, _⟩ := bh4_trivial_theta_witness X
  exact ⟨A, hθ⟩

example : ∃ _A : bh4_AHData X, ∀ (_l : abelianPeriodLattice X) (p : Fin (dim X.left) → ℂ),
    AreAssociatedAt (fun _ ↦ (1 : ℂ)) (fun _ ↦ 1) p := by
  obtain ⟨A, _, hθ, _⟩ := bh4_trivial_theta_witness X
  exact ⟨A, fun l p ↦ spec_bh4_theta_translation_associated X A _ hθ l p⟩

-- Nonzero-germ premises are witnessed without theta existence or positivity.
example : ∃ θ : (Fin (dim X.left) → ℂ) → ℂ, Differentiable ℂ θ ∧ θ ≠ 0 := by
  exact ⟨fun _ ↦ 1, differentiable_const 1, fun h ↦ one_ne_zero (congrFun h 0)⟩

-- Local-data assembly has a unit equation, nonzero germs and translation association.
example : ∃ θ : (Fin (dim X.left) → ℂ) → ℂ,
    Differentiable ℂ θ ∧ (∀ p, ¬ ∀ᶠ z in nhds p, θ z = 0) ∧
      (∀ (l : abelianPeriodLattice X) p, AreAssociatedAt θ (fun z ↦ θ (z + l)) p) := by
  refine ⟨fun _ ↦ 1, differentiable_const 1,
    fun _ h ↦ one_ne_zero h.self_of_nhds, ?_⟩
  intro l p
  exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
    Eventually.of_forall fun _ ↦ (one_mul _).symm⟩

-- Polarization has no additional datum premise; the ambient family has trivial AH data.
example : Nonempty (bh4_AHData X) := by
  obtain ⟨A, _⟩ := bh4_trivial_theta_witness X
  exact ⟨A⟩

-- Domination has positive input even in dimension zero; no positivity assumption is reused.
example (hg : dim X.left = 0) :
    ∃ _H H₀ : HermitianForm (V := Fin (dim X.left) → ℂ), H₀.IsPositiveDefinite := by
  refine ⟨HermitianForm.zero, HermitianForm.zero, ?_⟩
  intro v hv
  have : IsEmpty (Fin (dim X.left)) := by rw [hg]; infer_instance
  exact (hv (Subsingleton.elim v 0)).elim

-- The assembly premises allow the zero datum and the natural multiple zero.
example : ∃ _A _A₀ : bh4_AHData X, ∃ n : ℕ, n = 0 := by
  obtain ⟨A, _⟩ := bh4_trivial_theta_witness X
  exact ⟨A, A, 0, rfl⟩

-- Extensionality has the concrete pair of zero classes as a premise witness.
example : ∃ c d : HQ X 2,
    ∀ l m : abelianPeriodLattice X, bh4_periodPair X l m c = bh4_periodPair X l m d :=
  ⟨0, 0, fun _ _ ↦ rfl⟩

-- The lattice-pair formula has a zero-form witness on every ambient X.
example : ∃ A : bh4_AHData X, A.H = HermitianForm.zero := by
  obtain ⟨A, hA, _⟩ := bh4_trivial_theta_witness X
  exact ⟨A, hA⟩

-- The geometric period identity has a nonzero section and an empty algebraization witness.
example : ∃ A : bh4_AHData X,
    ∃ θ : (Fin (dim X.left) → ℂ) → ℂ,
      θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter) ∧ θ ≠ 0 ∧
      ∃ D : bh4_LocalDivisorData X, Nonempty (bh4_Algebraization X D) ∧
        (∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p) := by
  obtain ⟨A, _, hθ, D, hR, hlocal⟩ := bh4_trivial_theta_witness X
  exact ⟨A, fun _ ↦ 1, hθ, fun h ↦ one_ne_zero (congrFun h 0), D, hR, hlocal⟩

-- The Chern normalization premise is realized by the actual logarithmic form.
example : ∃ A : bh4_AHData X,
    ∃ E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ,
      ∀ l m, E' l m = chernForm
        (holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) l m := by
  obtain ⟨A, _⟩ := bh4_trivial_theta_witness X
  obtain ⟨E', hE', _⟩ := spec_chernClassHQ_datumOfX X A.H A.E A.integral A.chi
    A.semicharacter _ (spec_holLog_isLog _).1
    (spec_holLog_isLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)).2
  exact ⟨A, E', hE'⟩

-- Fundamental-class transport has an actual empty divisor algebraization.
example : ∃ D : bh4_LocalDivisorData X, Nonempty (bh4_Algebraization X D) := by
  obtain ⟨_, _, _, D, hR, _⟩ := bh4_trivial_theta_witness X
  exact ⟨D, hR⟩

-- Boundary avoidance has an entire unit-function witness for every pair of periods.
example (l m : abelianPeriodLattice X) :
    ∃ θ : (Fin (dim X.left) → ℂ) → ℂ, Differentiable ℂ θ ∧ θ ≠ 0 ∧
      ∃ z : Fin (dim X.left) → ℂ, ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
        θ (bh4_squareEdge X l m z i t) ≠ 0 := by
  exact ⟨fun _ ↦ 1, differentiable_const 1, fun h ↦ one_ne_zero (congrFun h 0),
    0, fun _ _ _ ↦ one_ne_zero⟩

-- Boundary logarithm lifting has the same nonvanishing continuous unit as input.
example (l m : abelianPeriodLattice X) :
    ∃ θ : (Fin (dim X.left) → ℂ) → ℂ, Continuous θ ∧
      ∃ z : Fin (dim X.left) → ℂ, ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
        θ (bh4_squareEdge X l m z i t) ≠ 0 :=
  ⟨fun _ ↦ 1, continuous_const, 0, fun _ _ _ ↦ one_ne_zero⟩

-- The Chern boundary calculation has actual zero logarithms of the unit theta section.
example (l m : abelianPeriodLattice X) :
    ∃ A : bh4_AHData X, ∃ θ : (Fin (dim X.left) → ℂ) → ℂ,
      θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter) ∧
      ∃ z : Fin (dim X.left) → ℂ, ∃ g : Fin 4 → ℝ → ℂ,
        (∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1)) ∧
        (∀ i t, t ∈ Icc (0 : ℝ) 1 →
          θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) := by
  obtain ⟨A, _, hθ, _⟩ := bh4_trivial_theta_witness X
  exact ⟨A, fun _ ↦ 1, hθ, 0, fun _ _ ↦ 0, fun _ ↦ continuousOn_const,
    fun _ _ _ ↦ by simp only [mul_zero, Complex.exp_zero]⟩

-- The boundary fundamental-class premise also has an empty algebraization, independently of GAGA.
example (l m : abelianPeriodLattice X) :
    ∃ θ : (Fin (dim X.left) → ℂ) → ℂ, Differentiable ℂ θ ∧ θ ≠ 0 ∧
      ∃ D : bh4_LocalDivisorData X, Nonempty (bh4_Algebraization X D) ∧
        (∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p) ∧
        ∃ z : Fin (dim X.left) → ℂ, ∃ g : Fin 4 → ℝ → ℂ,
          (∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1)) ∧
          (∀ i t, t ∈ Icc (0 : ℝ) 1 →
            θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) := by
  obtain ⟨_, _, _, D, hR, hlocal⟩ := bh4_trivial_theta_witness X
  exact ⟨fun _ ↦ 1, differentiable_const 1, fun h ↦ one_ne_zero (congrFun h 0),
    D, hR, hlocal, 0, fun _ _ ↦ 0, fun _ ↦ continuousOn_const,
    fun _ _ _ ↦ by simp only [mul_zero, Complex.exp_zero]⟩

-- The ambient geometric premises themselves have the concrete terminal group scheme witness.
example : ∃ A : bh4_AHData (𝟙_ (Over (Spec ↧ℂ))), A.H.IsPositiveDefinite := by
  let X₀ : Over (Spec ↧ℂ) := 𝟙_ (Over (Spec ↧ℂ))
  have hg : dim X₀.left = 0 := SmoothOfRelativeDimension.dim_eq X₀.hom 0
  obtain ⟨A, _, _, _⟩ := bh4_trivial_theta_witness X₀
  refine ⟨A, ?_⟩
  intro v hv
  have : IsEmpty (Fin (dim X₀.left)) := by rw [hg]; infer_instance
  exact (hv (Subsingleton.elim v 0)).elim

end HodgeLean.Adapters

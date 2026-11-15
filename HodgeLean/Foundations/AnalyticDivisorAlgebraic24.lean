import HodgeLean.Foundations.AnalyticDivisorAlgebraic24Proofs

/-! # Codimension one and complete algebraization

An implication from set-level Chow and period-invariant local divisor equations.
The geometric auxiliaries are open specification obligations. The dimension route
compares smooth charts; no general analytic dimension theory is postulated.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic24
open Filter Set Topology
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21
open HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open scoped Manifold CategoryTheory.MonObj

open HodgeLean.Foundations.AnalyticDivisorAlgebraic23

/-- Inverse analytic chart germs have equal complex dimensions.
Source: Lang, Real and Functional Analysis, third edition, Chapter XIV §1 (chain rule);
finite-dimensional linear algebra applied to the two derivatives. -/
theorem gaga24_chart_dimension {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] (a : E) (b : F) (u : E → F) (v : F → E)
    (hu : AnalyticAt ℂ u a) (hv : AnalyticAt ℂ v b)
    (hab : u a = b) (hba : v b = a)
    (hvu : ∀ᶠ z in 𝓝 a, v (u z) = z) (huv : ∀ᶠ z in 𝓝 b, u (v z) = z) :
    Module.finrank ℂ E = Module.finrank ℂ F :=
  gaga24_chart_dimension_aux a b u v hu hv hab hba hvu huv

/-- The smooth locus is dense in the analytic topology of the reduced component.
Source: Mumford, Algebraic Geometry I: Complex Projective Varieties, Chapter I §10;
Chirka, Complex Analytic Sets, §2.3 (regular points). -/
theorem gaga24_smooth_dense (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Dense (cycleComponentSmoothAnalyticLocus X x) :=
  gaga24_smooth_dense_aux X x

/-- A descended divisor component is proper and its generic point has positive coheight.
Source: Griffiths--Harris, Chapter 1 §1 (nonzero local divisor equations);
Mathlib `Order.coheight_eq_zero` and generic-point specialization. -/
theorem gaga24_proper (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (O : (gaga22_descendedOnX X hD hper).Component) :
    gaga23_carrier X hD hper hChow O ≠ univ ∧
      1 ≤ Order.coheight (gaga23_point X hD hper hChow O) :=
  gaga24_proper_aux X hD hper hChow O

/-- Each component has an algebraically smooth point with a regular analytic defining equation.
Source: Chirka §2.3 and §5.1; `gaga21_br_regular_locus_off`;
`gaga24_smooth_dense` and openness of the regular hypersurface locus. -/
theorem gaga24_common_regular (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (O : (gaga22_descendedOnX X hD hper).Component) :
    ∃ (p : Fin (dim X.left) → ℂ) (g : (Fin (dim X.left) → ℂ) → ℂ),
      abelianExp X p ∈ cycleComponentSmoothSupport X (gaga23_point X hD hper hChow O) ∧
      AnalyticAt ℂ g p ∧ g p = 0 ∧ fderiv ℂ g p ≠ 0 ∧
      (∀ᶠ z in 𝓝 p, g z = 0 ↔ abelianExp X z ∈
        gaga23_componentSupport X (gaga23_point X hD hper hChow O)) :=
  gaga24_common_regular_aux X hD hper hChow O

/-- Compare the algebraic smooth chart with the regular hypersurface graph chart.
Source: `gaga21_br_regular_graph_chart`; `ComplexPoint.localChart`;
`gaga24_chart_dimension` and rank-nullity for a nonzero complex linear functional. -/
theorem gaga24_component_dimension (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (O : (gaga22_descendedOnX X hD hper).Component) :
    ∃ m : ℕ, SmoothOfRelativeDimension m
      (cycleComponentSmoothLocusOver X (gaga23_point X hD hper hChow O)).hom ∧ m + 1 = dim X.left :=
  gaga24_component_dimension_aux X hD hper hChow O

/-- The constructed generic point of every descended component has coheight one.
Source: `cycleComponentSmoothLocus_smoothOfRelativeDimension`;
`gaga24_component_dimension`; `SmoothOfRelativeDimension.coheight_le_complex`. -/
theorem gaga24_codim (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (O : (gaga22_descendedOnX X hD hper).Component) :
    Order.coheight (gaga23_point X hD hper hChow O) = 1 :=
  gaga24_codim_aux X hD hper hChow O

/-- An implication from set-level Chow producing every field of the bh4 algebraization.
Source: Serre, GAGA, Théorème 3; `gaga23_indexing`, `gaga23_local_equations`,
and `gaga24_codim`. -/
theorem gaga24_algebraization (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    Nonempty (gaga24_Algebraization X V f) :=
  gaga24_algebraization_aux X hD hper hChow

/-- Set-level Chow for the fixed smooth projective cubic.
Source: Serre, Géométrie algébrique et géométrie analytique, Théorème 3;
Forster, Lectures on Riemann Surfaces, §1 (identity theorem). -/
theorem gaga24_curve_chow (Z : Set (ComplexPoint Curves.E))
    (hZ : IsClosedAnalytic (Fin (dim Curves.E.left) → ℂ) Z) :
    ∃ C : Set Curves.E.left, IsClosed C ∧
      Z = (Point.underlying : ComplexPoint Curves.E → Curves.E.left) ⁻¹' C :=
  gaga24_curve_chow_aux Z hZ

end HodgeLean.Foundations.AnalyticDivisorAlgebraic24

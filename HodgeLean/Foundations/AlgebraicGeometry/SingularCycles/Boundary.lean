import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryProofs

/-! # Retained boundaries and extension of supported equality

These signatures concern the retained algebraic bad set and supported
restriction on a smooth source. Flatness is asserted only on the retained
open. Every component over its complement remains visible.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
open scoped Classical
namespace AlgebraicGeometry.SingularCycles

/-- The intrinsic bad locus is a closed subset for a finite map to a finite-type target.
Source: EGA IV, 11.1.1; Stacks Project, Tags 052B and 01WM. -/
theorem actualBadLocus_isClosed
    {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [IsReduced Z]
    (f : X ⟶ Z) [IsFinite f] : IsClosed (actualBadLocus q f) :=
  actualBadLocus_isClosed_aux q f

example {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (f : X ⟶ Z) :
    IsClosed ((actualGoodOpen q f : Set Z)ᶜ) := (actualGoodOpen q f).isOpen.isClosed_compl

/-- No generic target point belongs to the intrinsic bad locus.
Source: EGA IV, 6.9.1; Stacks Project, Tag 052B. -/
theorem actualBadLocus_coheight
    {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [IsReduced Z]
    (f : X ⟶ Z) [IsFinite f] :
    ∀ z ∈ actualBadLocus q f, (1 : ℕ∞) ≤ Order.coheight z :=
  actualBadLocus_coheight_aux q f

example {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (f : X ⟶ Z) (z : Z)
    (hz : z ∉ q.smoothLocus) : z ∈ actualBadLocus q f := Or.inl hz

/-- The canonical open has exactly the intrinsic bad locus as complement.
Source: EGA IV, 11.1.1; Stacks Project, Tag 052B. -/
theorem actualGoodOpen_complement
    {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [IsReduced Z]
    (f : X ⟶ Z) [IsFinite f] :
    (actualGoodOpen q f : Set Z)ᶜ = actualBadLocus q f :=
  actualGoodOpen_complement_aux q f

example {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (f : X ⟶ Z) (x : X)
    (hx : ¬ (f.stalkMap x).hom.Flat) : f x ∈ actualBadLocus q f :=
  Or.inr ⟨x, hx, rfl⟩

/-- On the intrinsic complement the target is smooth and the finite map is flat.
Source: EGA IV, 6.9.1; Stacks Project, Tags 052B and 01V7. -/
theorem actualGoodOpen_smooth_flat
    {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [IsReduced Z]
    (f : X ⟶ Z) [IsFinite f] :
    Smooth ((actualGoodOpen q f).ι ≫ q) ∧ Flat (f ∣_ actualGoodOpen q f) :=
  actualGoodOpen_smooth_flat_aux q f

example : Smooth (𝟙 (Spec (CommRingCat.of ℂ))) ∧
    Flat (𝟙 (Spec (CommRingCat.of ℂ))) := ⟨inferInstance, inferInstance⟩

/-- A reduced finite-type target has a dense smooth open on which the retained finite map is flat.
Source: EGA IV, 6.9.1; Stacks Project, Tags 052B and 01V7. -/
theorem retained_flat_open
    {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [IsReduced Z]
    (f : X ⟶ Z) [IsFinite f] :
    ∃ U : Z.Opens, Dense (retainedOpen q U : Set Z) ∧
      Smooth ((retainedOpen q U).ι ≫ q) ∧ Flat (f ∣_ retainedOpen q U) :=
  retained_flat_open_aux q f

example := retained_flat_open_wrong_empty

/-- All collected generic components above the bad target are retained, including their weights.
Source: Fulton, Intersection Theory, second edition, §§1.5 and 1.7. -/
theorem boundary_component_accounting
    {X Z : Scheme.{0}} (f : X ⟶ Z) (D : Closeds Z) (b : X →₀ ℚ) :
    boundaryPart f D b + (b - boundaryPart f D b) = b ∧
      (∀ x, boundaryPart f D b x = if f x ∈ D then b x else (0 : ℚ)) ∧
      (∀ x, x ∈ (boundaryPart f D b).support ↔ x ∈ b.support ∧ f x ∈ D) :=
  boundary_component_accounting_aux f D b

example := boundary_component_accounting_wrong_drop

/-- A higher-coheight boundary is equivalent to retaining every component of the critical coheight.
Source: Fulton, Intersection Theory, second edition, §1.5; Mathlib Order.coheight_add_one_le. -/
theorem boundary_coheight_criterion
    {X Z : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ℂ))
    [QuasiCompact s] (f : X ⟶ Z) (D : Closeds Z) (b : X →₀ ℚ) (k : ℕ)
    (hk : ∀ x ∈ b.support, (k : ℕ∞) ≤ Order.coheight x) :
    (∀ x ∈ sourceBoundary s f D b, ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight x) ↔
      ∀ x ∈ (boundaryPart f D b).support, ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight x :=
  boundary_coheight_criterion_aux s f D b k hk

example := boundary_coheight_criterion_wrong_omission

/-- Purity annihilates the two obstruction degrees after the component criterion has been verified on the smooth source.
Source: Borel–Haefliger, La classe d’homologie fondamentale d’un espace analytique, §2; a3b4a_classRelative_purity_vanishing. -/
theorem boundary_support_purity
    {X Z : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ℂ))
    [Smooth s] [QuasiCompact s] [IsSeparated s]
    (f : X ⟶ Z) (D : Closeds Z) (b : X →₀ ℚ) (k : ℕ)
    (hk : ∀ x ∈ b.support, (k : ℕ∞) ≤ Order.coheight x)
    (hbad : ∀ x ∈ (boundaryPart f D b).support,
      ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight x)
    (V : Opens (ComplexPoint (Over.mk s))) (j : ℕ) (hj : j < 2 * (k + 1)) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (V : Set (ComplexPoint (Over.mk s)))
        (Point.underlying ⁻¹' (sourceBoundary s f D b : Set X))) j) :=
  boundary_support_purity_aux s f D b k hk hbad V j hj

example := boundary_support_purity_wrong_codimension

/-- Supported equality on the boundary complement extends uniquely on a smooth source once every bad component passes the coheight test.
Source: Hatcher, Algebraic Topology, §3.1; a3b4a_classCycle_restriction_bijective_of_boundary_codimension. -/
theorem boundary_restriction_bijective
    {X Z : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ℂ))
    [Smooth s] [QuasiCompact s] [IsSeparated s]
    (f : X ⟶ Z) (D : Closeds Z) (b : X →₀ ℚ) (k : ℕ)
    (hk : ∀ x ∈ b.support, (k : ℕ∞) ≤ Order.coheight x)
    (hbad : ∀ x ∈ (boundaryPart f D b).support,
      ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight x) :
    Function.Bijective (boundaryRestriction s f D b k) :=
  boundary_restriction_bijective_aux s f D b k hk hbad

example := boundary_restriction_bijective_wrong_boundary

/-- Every actual inverse-image generic component over the bad set retains its positive finite stalk length.
Source: Fulton, Intersection Theory, second edition, §§1.5 and 1.7;
`ccm3_flatPullbackPrime_coeff` and `ccm3_genericLength_finite_pos`. -/
theorem inverse_bad_component_length
    {X Z : Over (Spec (CommRingCat.of ℂ))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme)
    (D : Closeds Z.left) (hD : f.left ((ccm3_inverseIdeal f.left x).subschemeι y) ∈ D) :
    boundaryPart f.left D (inverseCoefficients f x)
        ((ccm3_inverseIdeal f.left x).subschemeι y) =
      (genericMultiplicity f.left x y (ccm3_genericLength_finite_pos f x y hy).2 : ℚ) ∧
    ((ccm3_inverseIdeal f.left x).subschemeι y) ∈
      (boundaryPart f.left D (inverseCoefficients f x)).support :=
  inverse_bad_component_length_aux f x y hy D hD

example := inverse_bad_component_length_wrong_discard

end AlgebraicGeometry.SingularCycles

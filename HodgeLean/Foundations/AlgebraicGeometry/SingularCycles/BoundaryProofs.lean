import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryChecks
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryFlatHelpers
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryFiniteOpen

/-! # Boundary purity obligations

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
theorem actualBadLocus_isClosed_aux
    {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [IsReduced Z]
    (f : X ⟶ Z) [IsFinite f] : IsClosed (actualBadLocus q f) := by
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian q
  exact q.smoothLocus.isOpen.isClosed_compl.union
    (boundary_finite_nonflat_image_closed f)

example {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (f : X ⟶ Z) :
    IsClosed ((actualGoodOpen q f : Set Z)ᶜ) := (actualGoodOpen q f).isOpen.isClosed_compl

/-- No generic target point belongs to the intrinsic bad locus.
Source: EGA IV, 6.9.1; Stacks Project, Tag 052B. -/
theorem actualBadLocus_coheight_aux
    {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [IsReduced Z]
    (f : X ⟶ Z) [IsFinite f] :
    ∀ z ∈ actualBadLocus q f, (1 : ℕ∞) ≤ Order.coheight z := by
  intro z hz
  by_contra h
  have hz0 : Order.coheight z = 0 := by
    simpa only [ENat.lt_one_iff_eq_zero] using lt_of_not_ge h
  rcases hz with hs | ⟨x, hx, rfl⟩
  · exact hs (boundary_generic_smooth q z hz0)
  · exact hx (RingHom.Flat.of_isField
      (isField_stalk_of_closure_mem_irreducibleComponents Z (f x)
        (boundary_generic_component (f x) hz0)) (f.stalkMap x).hom)

example {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (f : X ⟶ Z) (z : Z)
    (hz : z ∉ q.smoothLocus) : z ∈ actualBadLocus q f := Or.inl hz

/-- The canonical open has exactly the intrinsic bad locus as complement.
Source: EGA IV, 11.1.1; Stacks Project, Tag 052B. -/
theorem actualGoodOpen_complement_aux
    {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [IsReduced Z]
    (f : X ⟶ Z) [IsFinite f] :
    (actualGoodOpen q f : Set Z)ᶜ = actualBadLocus q f := by
  change (interior (actualBadLocus q f)ᶜ)ᶜ = actualBadLocus q f
  rw [(actualBadLocus_isClosed_aux q f).isOpen_compl.interior_eq, compl_compl]

example {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (f : X ⟶ Z) (x : X)
    (hx : ¬ (f.stalkMap x).hom.Flat) : f x ∈ actualBadLocus q f :=
  Or.inr ⟨x, hx, rfl⟩

/-- On the intrinsic complement the target is smooth and the finite map is flat.
Source: EGA IV, 6.9.1; Stacks Project, Tags 052B and 01V7. -/
theorem actualGoodOpen_smooth_flat_aux
    {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [IsReduced Z]
    (f : X ⟶ Z) [IsFinite f] :
    Smooth ((actualGoodOpen q f).ι ≫ q) ∧ Flat (f ∣_ actualGoodOpen q f) := by
  constructor
  · apply boundary_smooth_restrict
    intro z hz
    have hz' : z ∉ actualBadLocus q f := interior_subset hz
    exact not_not.mp (fun hs => hz' (Or.inl hs))
  · apply boundary_flat_restrict
    intro x hx
    have hx' : f x ∉ actualBadLocus q f := interior_subset hx
    exact not_not.mp (fun h => hx' (Or.inr ⟨x, h, rfl⟩))

example : Smooth (𝟙 (Spec (CommRingCat.of ℂ))) ∧
    Flat (𝟙 (Spec (CommRingCat.of ℂ))) := ⟨inferInstance, inferInstance⟩

/-- A reduced finite-type target has a dense smooth open on which the retained finite map is flat.
Source: EGA IV, 6.9.1; Stacks Project, Tags 052B and 01V7. -/
theorem retained_flat_open_aux
    {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [IsReduced Z]
    (f : X ⟶ Z) [IsFinite f] :
    ∃ U : Z.Opens, Dense (retainedOpen q U : Set Z) ∧
      Smooth ((retainedOpen q U).ι ≫ q) ∧ Flat (f ∣_ retainedOpen q U) := by
  obtain ⟨U, hU, hflat⟩ := boundary_reduced_generic_flat q f
  refine ⟨U, ?_, boundary_smooth_restrict q _ inf_le_right, ?_⟩
  · exact hU.inter_of_isOpen_right q.dense_smoothLocus_of_perfectField
      q.smoothLocus.isOpen
  · apply boundary_flat_restrict
    intro x hx
    letI := hflat
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap f U ⟨x, hx.1⟩)).mp (Flat.stalkMap _ _)

example := retained_flat_open_wrong_empty

/-- All collected generic components above the bad target are retained, including their weights.
Source: Fulton, Intersection Theory, second edition, §§1.5 and 1.7. -/
theorem boundary_component_accounting_aux
    {X Z : Scheme.{0}} (f : X ⟶ Z) (D : Closeds Z) (b : X →₀ ℚ) :
    boundaryPart f D b + (b - boundaryPart f D b) = b ∧
      (∀ x, boundaryPart f D b x = if f x ∈ D then b x else (0 : ℚ)) ∧
      (∀ x, x ∈ (boundaryPart f D b).support ↔ x ∈ b.support ∧ f x ∈ D) := by
  refine ⟨add_sub_cancel _ _, ?_, ?_⟩
  · intro x
    exact Finsupp.filter_apply _ _ _
  · intro x
    simp only [boundaryPart, Finsupp.mem_support_iff, Finsupp.filter_apply]
    by_cases h : f x ∈ D <;> simp [h]

example := boundary_component_accounting_wrong_drop

/-- A higher-coheight boundary is equivalent to retaining every component of the critical coheight.
Source: Fulton, Intersection Theory, second edition, §1.5; Mathlib Order.coheight_add_one_le. -/
theorem boundary_coheight_criterion_aux
    {X Z : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ℂ))
    [QuasiCompact s] (f : X ⟶ Z) (D : Closeds Z) (b : X →₀ ℚ) (k : ℕ)
    (hk : ∀ x ∈ b.support, (k : ℕ∞) ≤ Order.coheight x) :
    (∀ x ∈ sourceBoundary s f D b, ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight x) ↔
      ∀ x ∈ (boundaryPart f D b).support, ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight x := by
  have hsupport (x : X) :
      x ∈ (boundaryPart f D b).support ↔ x ∈ b.support ∧ f x ∈ D :=
    (boundary_component_accounting_aux f D b).2.2 x
  constructor
  · intro h x hx
    obtain ⟨hxb, hxD⟩ := (hsupport x).mp hx
    apply h x
    refine ⟨?_, hxD⟩
    exact Set.mem_iUnion₂.mpr ⟨x, (boundary_collected_support b x).mpr hxb,
      subset_closure (Set.mem_singleton x)⟩
  · intro h x hx
    obtain ⟨ξ, hξ, hxξ⟩ := Set.mem_iUnion₂.mp hx.1
    have hξb := (boundary_collected_support b ξ).mp hξ
    by_cases he : x = ξ
    · subst x
      exact h ξ ((hsupport ξ).mpr ⟨hξb, hx.2⟩)
    · have hle : x ≤ ξ :=
        Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hxξ)
      have hlt : x < ξ := lt_iff_le_not_ge.mpr ⟨hle, fun hge =>
        he (((Scheme.le_iff_specializes.mp hge).antisymm
          (Scheme.le_iff_specializes.mp hle)).eq)⟩
      calc
        ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by norm_cast
        _ ≤ Order.coheight ξ + 1 := by
          simpa only [add_comm] using add_le_add_right (hk ξ hξb) 1
        _ ≤ Order.coheight x := Order.coheight_add_one_le hlt

example := boundary_coheight_criterion_wrong_omission

/-- Purity annihilates the two obstruction degrees after the component criterion has been verified on the smooth source.
Source: Borel–Haefliger, La classe d’homologie fondamentale d’un espace analytique, §2; a3b4a_classRelative_purity_vanishing. -/
theorem boundary_support_purity_aux
    {X Z : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ℂ))
    [Smooth s] [QuasiCompact s] [IsSeparated s]
    (f : X ⟶ Z) (D : Closeds Z) (b : X →₀ ℚ) (k : ℕ)
    (hk : ∀ x ∈ b.support, (k : ℕ∞) ≤ Order.coheight x)
    (hbad : ∀ x ∈ (boundaryPart f D b).support,
      ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight x)
    (V : Opens (ComplexPoint (Over.mk s))) (j : ℕ) (hj : j < 2 * (k + 1)) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (V : Set (ComplexPoint (Over.mk s)))
        (Point.underlying ⁻¹' (sourceBoundary s f D b : Set X))) j) := by
  exact a3b4a_classRelative_purity_vanishing s (sourceBoundary s f D b) (k + 1)
    ((boundary_coheight_criterion_aux s f D b k hk).mpr hbad) V j hj

example := boundary_support_purity_wrong_codimension

/-- Supported equality on the boundary complement extends uniquely on a smooth source once every bad component passes the coheight test.
Source: Hatcher, Algebraic Topology, §3.1; a3b4a_classCycle_restriction_bijective_of_boundary_codimension. -/
theorem boundary_restriction_bijective_aux
    {X Z : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ℂ))
    [Smooth s] [QuasiCompact s] [IsSeparated s]
    (f : X ⟶ Z) (D : Closeds Z) (b : X →₀ ℚ) (k : ℕ)
    (hk : ∀ x ∈ b.support, (k : ℕ∞) ≤ Order.coheight x)
    (hbad : ∀ x ∈ (boundaryPart f D b).support,
      ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight x) :
    Function.Bijective (boundaryRestriction s f D b k) := by
  exact a3b4a_classCycle_restriction_bijective_of_boundary_codimension s
    (collectedCycle b) k (sourceBoundary s f D b) inf_le_left
    ((boundary_coheight_criterion_aux s f D b k hk).mpr hbad)

example := boundary_restriction_bijective_wrong_boundary

/-- Every actual inverse-image generic component over the bad set retains its positive finite stalk length.
Source: Fulton, Intersection Theory, second edition, §§1.5 and 1.7;
`ccm3_flatPullbackPrime_coeff` and `ccm3_genericLength_finite_pos`. -/
theorem inverse_bad_component_length_aux
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
      (boundaryPart f.left D (inverseCoefficients f x)).support := by
  have hcoeff : inverseCoefficients f x
      ((ccm3_inverseIdeal f.left x).subschemeι y) =
      (genericMultiplicity f.left x y (ccm3_genericLength_finite_pos f x y hy).2 : ℚ) := by
    exact ccm3_flatPullbackPrime_coeff f x y hy
  constructor
  · rw [(boundary_component_accounting_aux f.left D (inverseCoefficients f x)).2.1,
      if_pos hD, hcoeff]
  · apply ((boundary_component_accounting_aux f.left D
      (inverseCoefficients f x)).2.2 _).mpr
    refine ⟨?_, hD⟩
    rw [Finsupp.mem_support_iff]
    exact (ccm3_flatPullbackPrime_support f x _).mpr ⟨y, rfl, hy⟩

example := inverse_bad_component_length_wrong_discard

end AlgebraicGeometry.SingularCycles

import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryDefs
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CohomologyZero

/-! # Independent boundary tests

A nonzero rational cycle on the complex point tests retained components and
the necessity of the boundary coheight bound. No stage obligation is imported.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Convexity CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
open scoped Classical Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.SingularCycles

private abbrev P := Spec (CommRingCat.of ℂ)
private abbrev q : P ⟶ Spec (CommRingCat.of ℂ) := 𝟙 P
private abbrev CP := ComplexPoint (Over.mk q)
private def pt : CP := 𝟙 (Over.mk q)
private instance : Unique CP where
  default := pt
  uniq x := Over.mkIdTerminal.hom_ext x pt
private def p : P := pt.underlying
private def weights : P →₀ ℚ := Finsupp.single p (2 : ℚ)
private def D : Closeds P := targetBoundary q ⊥
private def B : Closeds P := sourceBoundary q (𝟙 P) D weights

private theorem D_full : D = ⊤ := by
  ext x
  simp [D, targetBoundary, retainedOpen]

private theorem cycle_two : collectedCycle weights =
    Function.locallyFinsuppWithin.single p (2 : ℚ) := by
  simp [collectedCycle, weights]

private theorem B_full : B = ⊤ := by
  ext x
  have hx : x = p := Subsingleton.elim _ _
  subst x
  simp [B, sourceBoundary, D_full, a3b4a_classAlgebraicSupport, cycle_two,
    subset_closure (Set.mem_singleton p)]

private theorem point_actual_bad_empty : actualBadLocus q (𝟙 P) = ∅ := by
  ext z
  simp only [actualBadLocus, q.smoothLocus_eq_top, Opens.coe_top, Set.compl_univ,
    Set.empty_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_exists, not_and]
  intro x hx
  exact (hx (Flat.stalkMap (𝟙 P) x)).elim

private theorem point_actual_good_top : actualGoodOpen q (𝟙 P) = ⊤ := by
  ext z
  simp [actualGoodOpen, point_actual_bad_empty]

/-- The intrinsic construction excludes no point of the smooth flat identity map.
Source: Stacks Project, Tags 052B and 01V7. -/
theorem actual_locus_identity_evaluation :
    IsClosed (actualBadLocus q (𝟙 P)) ∧
    (∀ z ∈ actualBadLocus q (𝟙 P), (1 : ℕ∞) ≤ Order.coheight z) ∧
    (actualGoodOpen q (𝟙 P) : Set P)ᶜ = actualBadLocus q (𝟙 P) ∧
    Smooth ((actualGoodOpen q (𝟙 P)).ι ≫ q) ∧
    Flat ((𝟙 P) ∣_ actualGoodOpen q (𝟙 P)) := by
  rw [point_actual_bad_empty, point_actual_good_top]
  exact ⟨isClosed_empty, by simp, by simp, inferInstance, inferInstance⟩

example : actualBadLocus q (𝟙 P) ≠ (D : Set P) := by
  rw [point_actual_bad_empty, D_full, Closeds.coe_top]
  exact Set.empty_ne_univ

#print axioms actual_locus_identity_evaluation

/-- Dropping density permits an empty retained open even for a nonzero finite map.
Source: EGA IV, 6.9.1. -/
theorem retained_flat_open_wrong_empty :
    ¬ Dense (retainedOpen q (⊥ : P.Opens) : Set P) := by
  simpa [retainedOpen] using (Set.empty_ne_univ : (∅ : Set P) ≠ Set.univ)

example : Dense (retainedOpen q (⊤ : P.Opens) : Set P) ∧
    Flat ((𝟙 P) ∣_ retainedOpen q (⊤ : P.Opens)) := by
  constructor
  · simp [retainedOpen, q.smoothLocus_eq_top]
  · infer_instance

example : ¬ Dense (retainedOpen q (⊥ : P.Opens) : Set P) :=
  retained_flat_open_wrong_empty

/-- The actual bad summand has coefficient two, so deleting it changes the cycle.
Source: Fulton, Intersection Theory, second edition, §1.5. -/
theorem boundary_component_accounting_wrong_drop :
    boundaryPart (𝟙 P) D weights p ≠ (0 : ℚ) := by
  rw [D_full]
  change (if p ∈ (⊤ : Closeds P) then weights p else 0) ≠ 0
  rw [ite_eq_left (show p ∈ (⊤ : Closeds P) from Set.mem_univ _)]
  norm_num [weights]

example : boundaryPart (𝟙 P) D weights p ≠ (0 : ℚ) :=
  boundary_component_accounting_wrong_drop

/-- A component lying entirely above the bad set prevents a strict coheight gain.
Source: Mathlib Order.coheight_eq_zero. -/
theorem boundary_coheight_criterion_wrong_omission :
    p ∈ B ∧ ¬ ((1 : ℕ) : ℕ∞) ≤ Order.coheight p := by
  have hp : Order.coheight p = 0 := Order.IsMax.coheight_eq_zero
    (show IsMax p from fun _ _ => le_of_eq (Subsingleton.elim _ _))
  rw [B_full, hp]
  exact ⟨Set.mem_univ _, by norm_num⟩

example : p ∈ B ∧ ¬ ((1 : ℕ) : ℕ∞) ≤ Order.coheight p :=
  boundary_coheight_criterion_wrong_omission

private def emptySubspaceEquiv (A : TopPair.{0}) [IsEmpty A.snd] (n : ℕ) :
    RelativeCohomology ℚ A n ≃ₗ[ℚ] Cohomology ℚ A.fst n := by
  have hzero : ((chainPairFunctor ℚ).obj A).hom = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    change (SSet.chainComplexMap (TopCat.toSSet.map A.map) (ModuleCat.of ℚ ℚ)).f i = 0
    apply SSet.chainComplex_hom_ext
    intro σ
    exact isEmptyElim ((A.snd.toSSetObjEquiv _) σ StdSimplex.barycenter)
  haveI : IsIso (relativeChainProjection ℚ A) := cokernel.π_of_zero hzero
  let e := HomologicalComplex.homologyMapIso
    (HomologicalComplex.linearDualIso (asIso (relativeChainProjection ℚ A))) n
  exact LinearEquiv.ofBijective (relativeCohomologyToAbsolute ℚ A n)
    ((ConcreteCategory.isIso_iff_bijective e.hom).mp e.isIso_hom)

private def boundaryPair : TopPair := neighborhoodSupportComplementPair
    (Set.univ : Set CP) (Point.underlying ⁻¹' (B : Set P))

private instance : IsEmpty boundaryPair.snd := ⟨fun x => by
  have hx := x.2
  apply hx
  change x.1.1.underlying ∈ B
  have hm : ∀ z : P, z ∈ B := by rw [B_full]; exact fun _ => Set.mem_univ _
  exact hm _⟩

private instance : Unique boundaryPair.fst where
  default := ⟨pt, Set.mem_univ _⟩
  uniq x := Subtype.ext (Subsingleton.elim _ _)


private def boundaryUnit : RelativeCohomology ℚ boundaryPair (0 : ℕ) :=
  (emptySubspaceEquiv boundaryPair (0 : ℕ)).symm (cohomologyUnitZero ℚ boundaryPair.fst)

private theorem boundaryUnit_ne_zero : boundaryUnit ≠ 0 := by
  intro h
  have hh := congrArg (emptySubspaceEquiv boundaryPair (0 : ℕ)) h
  simp only [boundaryUnit, LinearEquiv.apply_symm_apply, map_zero] at hh
  exact cohomologyUnitZero_ne_zero ℚ boundaryPair.fst hh

/-- Without the coheight bound, the actual boundary pair has a nonzero degree-zero class.
Source: Hatcher, Algebraic Topology, §3.1. -/
theorem boundary_support_purity_wrong_codimension :
    ¬ IsZero (RelativeCohomology ℚ boundaryPair (0 : ℕ)) := by
  intro h
  letI := ModuleCat.subsingleton_of_isZero h
  exact boundaryUnit_ne_zero (Subsingleton.elim _ _)

example : ¬ IsZero (RelativeCohomology ℚ boundaryPair (0 : ℕ)) :=
  boundary_support_purity_wrong_codimension

private def supportPair : TopPair := TopPair.ofSubset
    (X := a3b4_an q) (a3b4_cycleSupport q (collectedCycle weights))ᶜ

private theorem support_full : a3b4_cycleSupport q (collectedCycle weights) = Set.univ := by
  rw [cycle_two]
  ext x
  have hx : x.underlying = p := congrArg Point.underlying (Subsingleton.elim x pt)
  simp [a3b4_cycleSupport, hx, subset_closure (Set.mem_singleton p)]

private instance : IsEmpty supportPair.snd := ⟨fun x => by
  have hx := x.2
  change x.1 ∉ a3b4_cycleSupport q (collectedCycle weights) at hx
  have hm : ∀ z : CP, z ∈ a3b4_cycleSupport q (collectedCycle weights) := by
    rw [support_full]; exact fun _ => Set.mem_univ _
  exact hx (hm _)⟩

private def supportUnit : RelativeCohomology ℚ supportPair (0 : ℕ) :=
  (emptySubspaceEquiv supportPair (0 : ℕ)).symm (cohomologyUnitZero ℚ (a3b4_an q))

private theorem supportUnit_ne_zero : supportUnit ≠ 0 := by
  intro h
  have hh := congrArg (emptySubspaceEquiv supportPair (0 : ℕ)) h
  change (emptySubspaceEquiv supportPair (0 : ℕ)) ((emptySubspaceEquiv supportPair (0 : ℕ)).symm _) = _ at hh
  rw [LinearEquiv.apply_symm_apply, map_zero] at hh
  exact cohomologyUnitZero_ne_zero ℚ (a3b4_an q) hh

/-- Removing an entire component kills its nonzero supported class.
Source: Hatcher, Algebraic Topology, §3.1, relative localization. -/
theorem boundary_restriction_bijective_wrong_boundary :
    ¬ Function.Injective (boundaryRestriction q (𝟙 P) D weights 0) := by
  intro hi
  apply supportUnit_ne_zero
  apply hi
  letI := neighborhoodSupportRelativeCohomology_subsingleton (a3b4_an q)
    (a3b4_cycleSupport q (collectedCycle weights)) 0
    (Point.underlying ⁻¹' (sourceBoundary q (𝟙 P) D weights : Set P))ᶜ
    (by intro x hx; exact (hx (show x.underlying ∈ B by rw [B_full]; trivial)).elim)
  exact Subsingleton.elim _ _

example : ¬ Function.Injective (boundaryRestriction q (𝟙 P) D weights 0) :=
  boundary_restriction_bijective_wrong_boundary

/-- Deleting the bad summand erases the actual scheme inverse-image cycle of the identity.
Source: Fulton, Intersection Theory, second edition, §1.7;
`ccm3_flatPullbackPrime_ne_zero`. -/
theorem inverse_bad_component_length_wrong_discard :
    boundaryPart (𝟙 P) D (inverseCoefficients (𝟙 (Over.mk q)) p) ≠ 0 := by
  intro h
  apply ccm3_flatPullbackPrime_ne_zero (𝟙 (Over.mk q)) p
  ext z
  have hh := congrArg (fun b => b z) h
  rw [D_full] at hh
  change (if z ∈ (⊤ : Closeds P) then
    ccm3_flatPullbackPrime (𝟙 P) p z else 0) = 0 at hh
  rw [ite_eq_left (show z ∈ (⊤ : Closeds P) from Set.mem_univ _)] at hh
  exact hh

example := inverse_bad_component_length_wrong_discard

/-- An actual inverse-image component need not acquire positive coheight above a supplied boundary.
Source: Fulton, Intersection Theory, second edition, §1.7. -/
theorem inverse_component_wrong_codimension :
    ∃ z ∈ (boundaryPart (𝟙 P) D (inverseCoefficients (𝟙 (Over.mk q)) p)).support,
      ¬ (1 : ℕ∞) ≤ Order.coheight z := by
  obtain ⟨z, hz⟩ := Finsupp.support_nonempty_iff.mpr
    inverse_bad_component_length_wrong_discard
  refine ⟨z, hz, ?_⟩
  have hzero : Order.coheight z = (0 : ℕ∞) :=
    Order.IsMax.coheight_eq_zero (show IsMax z from fun _ _ =>
      le_of_eq (Subsingleton.elim _ _))
  rw [hzero]
  norm_num

example : ∃ z ∈ (boundaryPart (𝟙 P) D (inverseCoefficients (𝟙 (Over.mk q)) p)).support,
    ¬ (1 : ℕ∞) ≤ Order.coheight z := inverse_component_wrong_codimension

#print axioms inverse_component_wrong_codimension

#print axioms retained_flat_open_wrong_empty
#print axioms boundary_component_accounting_wrong_drop
#print axioms boundary_coheight_criterion_wrong_omission
#print axioms boundary_support_purity_wrong_codimension
#print axioms boundary_restriction_bijective_wrong_boundary
#print axioms inverse_bad_component_length_wrong_discard

end AlgebraicGeometry.SingularCycles

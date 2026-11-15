import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Defs

/-! # Supports of inverse-image prime cycles

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters TopologicalSpace
namespace AlgebraicGeometry.SingularCycles

/-- The generic component closures cover the scheme-theoretic inverse image.
Source: Fulton, Intersection Theory, second edition, §1.5; Mathlib genericPoints.ofComponent. -/
theorem prime_cycle_algebraic_support {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    (⋃ ξ ∈ (ccm3_flatPullbackPrime f.left x).support, closure {ξ}) =
      ((ccm3_inverseIdeal f.left x).support : Set X.left) := by
  let I := ccm3_inverseIdeal f.left x
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨ξ, hξ, hz⟩
    obtain ⟨y, rfl, _⟩ := (ccm3_flatPullbackPrime_support f x ξ).mp hξ
    apply I.support.isClosed.closure_subset_iff.mpr _ hz
    intro w hw
    obtain rfl := Set.mem_singleton_iff.mp hw
    rw [← I.range_subschemeι]
    exact ⟨y, rfl⟩
  · intro hz
    obtain ⟨z', rfl⟩ := I.range_subschemeι.symm ▸ hz
    let C : irreducibleComponents I.subscheme :=
      ⟨irreducibleComponent z', irreducibleComponent_mem_irreducibleComponents z'⟩
    let y := (genericPoints.ofComponent C).1
    have hy : closure ({y} : Set I.subscheme) = C :=
      genericPoints.isGenericPoint_ofComponent C
    have hz' : z' ∈ closure ({y} : Set I.subscheme) :=
      hy.symm ▸ mem_irreducibleComponent
    refine ⟨I.subschemeι y,
      (ccm3_flatPullbackPrime_support f x _).mpr ⟨y, rfl, (genericPoints.ofComponent C).2⟩, ?_⟩
    have h := image_closure_subset_closure_image I.subschemeι.continuous
      (Set.mem_image_of_mem _ hz')
    simpa only [Set.image_singleton] using h

/-- A coefficient-one prime has its usual analytic support.
Source: Fulton, Intersection Theory, second edition, §1.5. -/
theorem prime_cycle_analytic_support (Z : Over (Spec ↧ℂ)) (x : Z.left) :
    a3b4_cycleSupport Z.hom (Function.locallyFinsuppWithin.single x (1 : ℚ)) =
      Point.underlying ⁻¹' closure {x} := by
  ext z
  simp [a3b4_cycleSupport, Function.locallyFinsuppWithin.single_apply,
    Function.locallyFinsuppWithin.support, Function.support]

end AlgebraicGeometry.SingularCycles

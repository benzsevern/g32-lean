import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.EtaleCoefficients

/-! # Separation of inverse-image prime components

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace HodgeLean.Adapters
namespace AlgebraicGeometry.SingularCycles

/-- Distinct generic components of a prime inverse image do not specialize to one another.
Source: Fulton, Intersection Theory, second edition, §1.5; maximality of irreducible components. -/
theorem prime_pullback_support_no_specialization {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (ξ η : X.left)
    (hξ : ccm3_flatPullbackPrime f.left x ξ ≠ 0)
    (hη : ccm3_flatPullbackPrime f.left x η ≠ 0)
    (h : ξ ∈ closure ({η} : Set X.left)) : ξ = η := by
  obtain ⟨y, rfl, hy⟩ := (ccm3_flatPullbackPrime_support f x ξ).mp hξ
  obtain ⟨z, rfl, hz⟩ := (ccm3_flatPullbackPrime_support f x η).mp hη
  let I := ccm3_inverseIdeal f.left x
  have hs : Specializes z y := I.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp
    (specializes_iff_mem_closure.mpr h)
  have hcl : closure ({y} : Set I.subscheme) = closure {z} := hy.eq_of_subset hz.1 hs.closure_subset
  have hyz : y = z := (inseparable_iff_closure_eq.mpr hcl).eq
  exact congrArg I.subschemeι hyz

end AlgebraicGeometry.SingularCycles

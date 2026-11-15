import HodgeLean.Foundations.Program.SchoenCycleC1FiniteFibreComplexPoints
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Basic

/-! Canonical generic fibre points for the actual finite normal-slice map. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- The inverse-image subscheme at the image of a complex point contains
that same source point as a component generic point. -/
theorem s4_q3_finite_point_inverse_component
    {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⟶ Z) [IsFinite f.left] (x : ComplexPoint X) :
    ∃ y : (ccm3_inverseIdeal f.left (Point.map f x).underlying).subscheme,
      (ccm3_inverseIdeal f.left (Point.map f x).underlying).subschemeι y = x.underlying ∧
      closure ({y} : Set (ccm3_inverseIdeal f.left (Point.map f x).underlying).subscheme) ∈
        irreducibleComponents (ccm3_inverseIdeal f.left (Point.map f x).underlying).subscheme := by
  let z := (Point.map f x).underlying
  let I := ccm3_inverseIdeal f.left z
  have hz : IsClosed ({z} : Set Z.left) :=
    ((pointEquivClosedPoint Z.hom) ⟨(Point.map f x).left, by simp⟩).2
  have hsupport : (I.support : Set X.left) = f.left ⁻¹' {z} := by
    dsimp only [I, ccm3_inverseIdeal]
    rw [Scheme.IdealSheafData.support_comap]
    change f.left ⁻¹' ((ccm3_primeIdeal Z.left z).support : Set Z.left) = _
    rw [ccm3_primeIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change f.left ⁻¹' closure ({z} : Set Z.left) = _
    rw [hz.closure_eq]
  have hx : x.underlying ∈ (I.support : Set X.left) := by
    rw [hsupport]
    exact Set.mem_singleton _
  obtain ⟨y, hy⟩ := I.range_subschemeι.symm ▸ hx
  let C := irreducibleComponent y
  have hsub : I.subschemeι '' C ⊆ f.left ⁻¹' {z} := by
    rintro _ ⟨w, _, rfl⟩
    rw [← hsupport, ← I.range_subschemeι]
    exact Set.mem_range_self w
  have hdisc := (f.left.isDiscrete_preimage_singleton z).mono hsub
  have hpre : IsPreirreducible (I.subschemeι '' C) :=
    isIrreducible_irreducibleComponent.isPreirreducible.image I.subschemeι
      I.subschemeι.continuous.continuousOn
  have hsingle : C = {y} := by
    apply Set.Subset.antisymm _ (Set.singleton_subset_iff.mpr mem_irreducibleComponent)
    intro w hw
    apply Set.mem_singleton_iff.mpr
    apply I.subschemeι.isClosedEmbedding.injective
    exact hdisc.subsingleton_of_isPreirreducible hpre
      ⟨w, hw, rfl⟩ ⟨y, mem_irreducibleComponent, rfl⟩
  refine ⟨y, hy, ?_⟩
  change closure ({y} : Set I.subscheme) ∈ irreducibleComponents I.subscheme
  rw [← hsingle, isClosed_irreducibleComponent.closure_eq]
  exact irreducibleComponent_mem_irreducibleComponents y

end HodgeLean.Foundations.Program

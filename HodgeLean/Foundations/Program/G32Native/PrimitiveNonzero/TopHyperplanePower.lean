import HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero.CoordinatePowerSpan
import HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero.TopComponent

/-! # Top powers of the normalized coordinate hyperplane class -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero

/-- The normalized coordinate hyperplane has a nonzero top cup power on its projective model.
Source: Fulton, Intersection Theory, second edition, §19.1; Hatcher, Algebraic Topology, §3.2.
HC no distance; AV milestone no distance. -/
theorem normalized_hyperplane_top_ne_zero
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (hH : IsIntegral (s2c_subscheme Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)).left)
    (cH : letI := hH
      s2e_supportedClass Q
        (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1)
    (hcH : letI := hH
      a3b4_IsCycleClass Q.hom
        (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH) :
    letI := hH
    s2e_hyperplanePower (TopCat.of (ComplexPoint Q))
      (s2e_classToAbsolute Q
        (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH) k ≠ 0 := by
  letI := hH
  let H := s2e_classToAbsolute Q
    (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH
  let T : Finset (Fin (k + 1)) := Finset.univ.erase 0
  have hcard : T.card = k := by simp [T]
  have hT : T.card ≤ k := hcard.le
  obtain ⟨hI, hsmI, hcI, -⟩ := coordinate_intersection_class Q k eQ T hT
  letI := hI
  have hc : Order.coheight
      ((s2c_subschemeι Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left
        (genericPoint (s2c_subscheme Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left)) = k := by
    simpa only [hcard] using hcI
  have hdim := s2e_projective_model_dimension Q k eQ
  letI : SmoothOfRelativeDimension k Q.hom := by
    rw [← hdim]
    infer_instance
  have hclass : coordinate_class_at_degree Q k eQ T hT k hcard ≠ 0 := by
    rw [coordinate_class_at_degree_eq Q k eQ T hT k hcard hc]
    exact top_component_class_ne_zero Q k _ hc
  have hsing : cupComparison Q (2 * k)
      (coordinate_class_at_degree Q k eQ T hT k hcard) ≠ 0 := by
    intro hz
    apply hclass
    exact (cupComparison Q (2 * k)).injective (by simpa only [map_zero] using hz)
  obtain ⟨r, hr⟩ := coordinate_power_span Q k eQ H
    (normalized_hyperplane_class_spans Q k hk eQ cH hcH) k T hT hcard hk
  intro hz
  apply hsing
  rw [hr, hz, smul_zero]

#print axioms normalized_hyperplane_top_ne_zero
end HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero

import HodgeLean.Foundations.Program.SchoenTransferQ3PointNormalOrientation
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Ramified
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreePointLength

/-! Ramified point pullback in the actual normal coordinates of a slice. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular AlgebraicGeometry.SingularCycles HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The ordered point class of a centred normal chart is nonzero. -/
theorem s4_q3_centred_point_class_ne_zero
    {M : Type} [TopologicalSpace M] [T1Space M] (d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (x : M) (hx : x ∈ e.source) (he : e x = 0) :
    localClassOfChart d (pointChart e) x ⟨hx, Set.mem_univ _⟩ ≠ 0 := by
  let V := flattenedSupportNeighborhood (Fin 0 → ℂ) d e x hx
  have hflat := s4_q3_zero_tangent_chart_flattens_point d e x hx he
  have hne := s4_q3_point_normal_orientation_ne_zero d e x hx he hflat
  intro hz
  apply hne
  unfold neighborhoodOrientation
  rw [hz, map_zero]

/-- On the actual flattened point neighbourhood, finite flat pullback has
the unreduced point-fibre length as its normal-coclass coefficient. -/
theorem s4_q3_finite_flat_slice_normal_coclass
    {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [Smooth X.hom] [Smooth Z.hom] [IsNoetherian Z.left]
    [T1Space (ComplexPoint X)] [T1Space (ComplexPoint Z)]
    (f : X ⟶ Z) [IsFinite f.left] [Flat f.left]
    (d : ℕ) (x : ComplexPoint X)
    (eX : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (eZ : OpenPartialHomeomorph (ComplexPoint Z) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (heX : a3b4_IsHolChart X.hom eX) (heZ : a3b4_IsHolChart Z.hom eZ)
    (hx : x ∈ eX.source) (hz : Point.map f x ∈ eZ.source)
    (hX0 : eX x = 0) (hZ0 : eZ (Point.map f x) = 0)
    (hisol : ∀ z ∈ flattenedSupportNeighborhood (Fin 0 → ℂ) d eX x hx,
      Point.map f z = Point.map f x → z = x)
    (y : (ccm3_inverseIdeal f.left (Point.map f x).underlying).subscheme)
    (hy : (ccm3_inverseIdeal f.left (Point.map f x).underlying).subschemeι y = x.underlying)
    (hfin : ccm3_genericLength f.left (Point.map f x).underlying y < ⊤) :
    relativeCohomologyMap ℚ (2 * d)
      (isolatedPairMap (TopCat.ofHom (Point.continuousMap f))
        (flattenedSupportNeighborhood (Fin 0 → ℂ) d eX x hx) x hisol)
      (normalizedRelativeCoclass
        (localClassOfChart d (pointChart eZ) (Point.map f x) ⟨hz, Set.mem_univ _⟩)
        (s4_q3_centred_point_class_ne_zero d eZ (Point.map f x) hz hZ0)) =
      ((pointFibreLength f.left x.underlying).toNat : ℚ) •
        chartNormalProjectionCoclass (Fin 0 → ℂ) d eX {x}
          (s4_q3_zero_tangent_chart_flattens_point d eX x hx hX0)
          (flattenedSupportNeighborhood (Fin 0 → ℂ) d eX x hx)
          (flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) d eX x hx) := by
  let V := flattenedSupportNeighborhood (Fin 0 → ℂ) d eX x hx
  have hflat := s4_q3_zero_tangent_chart_flattens_point d eX x hx hX0
  have hne := s4_q3_point_normal_orientation_ne_zero d eX x hx hX0 hflat
  have hcalc := finite_flat_local_coclass f d x eX eZ heX heZ
    ⟨hx, Set.mem_univ _⟩ ⟨hz, Set.mem_univ _⟩ V V.isOpen
    (mem_flattenedSupportNeighborhood (Fin 0 → ℂ) d eX x hx) hisol y hy hfin hne
    (s4_q3_centred_point_class_ne_zero d eZ (Point.map f x) hz hZ0)
  rw [s4_q3_point_neighborhood_coclass_eq_normal_coclass d eX x hx hX0 hflat] at hcalc
  have hlength := genericMultiplicity_eq_pointFibreLength f.left
    (Point.map f x).underlying y (by rw [hy]; rfl) hfin
  rw [hy] at hlength
  have hnat := congrArg ENat.toNat hlength
  simp only [ENat.toNat_coe] at hnat
  rw [← hnat]
  exact hcalc

end HodgeLean.Foundations.Program

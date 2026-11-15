import HodgeLean.Foundations.Program.SchoenTransferQ3RadialPointClass
import HodgeLean.Foundations.Program.SchoenTransferQ3PointChartSupport
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs

/-! Exact point orientation of the actual zero-tangential normal model. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- The flattened zero-tangential normal generator maps to the precisely
normalized point class of the actual point chart. -/
theorem s4_q3_point_normal_class_to_local_class
    {M : Type} [TopologicalSpace M] [T1Space M] (c : ℕ)
    (e : OpenPartialHomeomorph M ((Fin 0 → ℂ) × (Fin c → ℂ)))
    (x : M) (hx : x ∈ e.source) (he : e x = 0)
    (hflat : ∀ y ∈ e.source, y ∈ ({x} : Set M) ↔ (e y).2 = 0) :
    relativeHomologyMap ℚ (2 * c)
      (neighborhoodPointComplementPairMap (flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx) x)
      (flattenedSupportNormalClass (Fin 0 → ℂ) c e x hx {x} hflat
        (congrArg Prod.snd he)) =
      localClassOfChart c (pointChart e) x ⟨hx, Set.mem_univ _⟩ := by
  let j : neighborhoodSupportComplementPair
      (flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx) {x} ⟶ pointComplementPair x :=
    neighborhoodPointComplementPairMap (flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx) x
  change relativeHomologyMap ℚ (2 * c) j _ = _
  rw [flattenedSupportNormalClass_eq_normalFiber,
    ← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  apply s4_q3_radial_point_chart_class c (pointChart e) x ⟨hx, Set.mem_univ _⟩
    (flattenedSupportRadius (Fin 0 → ℂ) c e x hx)
    (flattenedSupportRadius_pos (Fin 0 → ℂ) c e x hx)
  · intro v
    change (flattenedSupportHomeomorph (Fin 0 → ℂ) c e x hx (0, v)).1 ∈
      (pointChart e).source
    exact ⟨flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) c e x hx
      (flattenedSupportHomeomorph (Fin 0 → ℂ) c e x hx (0, v)).2, Set.mem_univ _⟩
  · intro v
    change (e (flattenedSupportHomeomorph (Fin 0 → ℂ) c e x hx (0, v))).2 =
      OpenPartialHomeomorph.univBall (e x).2 _ v
    rw [flattenedSupportHomeomorph_coordinates, he]
    exact univBall_zero_tangent_normal (Fin 0 → ℂ) c 0 _
      (flattenedSupportRadius_pos (Fin 0 → ℂ) c e x hx) v

/-- Open excision identifies the actual point-neighbourhood orientation
with the flattened normal generator, retaining its exact normalization. -/
theorem s4_q3_point_neighborhood_orientation_eq_normal_class
    {M : Type} [TopologicalSpace M] [T1Space M] (c : ℕ)
    (e : OpenPartialHomeomorph M ((Fin 0 → ℂ) × (Fin c → ℂ)))
    (x : M) (hx : x ∈ e.source) (he : e x = 0)
    (hflat : ∀ y ∈ e.source, y ∈ ({x} : Set M) ↔ (e y).2 = 0) :
    neighborhoodOrientation c (pointChart e) x ⟨hx, Set.mem_univ _⟩
      (flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx)
      (flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx).isOpen
      (mem_flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx) =
    flattenedSupportNormalClass (Fin 0 → ℂ) c e x hx {x} hflat
      (congrArg Prod.snd he) := by
  let V := flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx
  have hxV := mem_flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx
  apply (neighborhoodPointComplement_relativeHomologyMap_bijective (V : Set M) x
    V.isOpen hxV (2 * c)).1
  calc
    _ = localClassOfChart c (pointChart e) x ⟨hx, Set.mem_univ _⟩ := by
      exact ConcreteCategory.congr_hom
        (Iso.inv_hom_id (neighborhoodPointComplementRelativeHomologyIso
          (V : Set M) x V.isOpen hxV (2 * c))) _
    _ = _ := (s4_q3_point_normal_class_to_local_class c e x hx he hflat).symm

/-- The actual point orientation on the flattened neighbourhood is nonzero. -/
theorem s4_q3_point_normal_orientation_ne_zero
    {M : Type} [TopologicalSpace M] [T1Space M] (c : ℕ)
    (e : OpenPartialHomeomorph M ((Fin 0 → ℂ) × (Fin c → ℂ)))
    (x : M) (hx : x ∈ e.source) (he : e x = 0)
    (hflat : ∀ y ∈ e.source, y ∈ ({x} : Set M) ↔ (e y).2 = 0) :
    neighborhoodOrientation c (pointChart e) x ⟨hx, Set.mem_univ _⟩
      (flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx)
      (flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx).isOpen
      (mem_flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx) ≠ 0 := by
  rw [s4_q3_point_neighborhood_orientation_eq_normal_class c e x hx he hflat]
  intro hz
  have h := chartNormalProjectionCoclass_apply_normalClass (Fin 0 → ℂ) c e {x}
    hflat x hx (congrArg Prod.snd he)
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- The normalized actual point-neighbourhood coclass is exactly the
normal-projection coclass in its centred point chart. -/
theorem s4_q3_point_neighborhood_coclass_eq_normal_coclass
    {M : Type} [TopologicalSpace M] [T1Space M] (c : ℕ)
    (e : OpenPartialHomeomorph M ((Fin 0 → ℂ) × (Fin c → ℂ)))
    (x : M) (hx : x ∈ e.source) (he : e x = 0)
    (hflat : ∀ y ∈ e.source, y ∈ ({x} : Set M) ↔ (e y).2 = 0) :
    normalizedRelativeCoclass
      (neighborhoodOrientation c (pointChart e) x ⟨hx, Set.mem_univ _⟩
        (flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx)
        (flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx).isOpen
        (mem_flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx))
      (s4_q3_point_normal_orientation_ne_zero c e x hx he hflat) =
    chartNormalProjectionCoclass (Fin 0 → ℂ) c e {x} hflat
      (flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx)
      (flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) c e x hx) := by
  have hclass := s4_q3_point_neighborhood_orientation_eq_normal_class c e x hx he hflat
  have hne : flattenedSupportNormalClass (Fin 0 → ℂ) c e x hx {x} hflat
      (congrArg Prod.snd he) ≠ 0 := by
    rw [← hclass]
    exact s4_q3_point_normal_orientation_ne_zero c e x hx he hflat
  have hnorm : normalizedRelativeCoclass _ hne =
      chartNormalProjectionCoclass (Fin 0 → ℂ) c e {x} hflat
        (flattenedSupportNeighborhood (Fin 0 → ℂ) c e x hx)
        (flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) c e x hx) := by
    apply chartNormalProjectionCoclass_unique (Fin 0 → ℂ) c e {x} hflat x hx
      (congrArg Prod.snd he)
    simp only [relativeCohomologyEquivDualHomology_normalizedRelativeCoclass,
      normalizedDual_apply_self]
  calc
    _ = normalizedRelativeCoclass _ hne := by congr 1
    _ = _ := hnorm

end HodgeLean.Foundations.Program

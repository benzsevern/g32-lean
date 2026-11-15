import HodgeLean.Foundations.Program.SchoenTransferQ3NeighbourhoodMaps
import HodgeLean.Foundations.Program.SchoenTransferQ3SliceSquare
import HodgeLean.Foundations.Program.SchoenTransferQ3FinitePointFibre
import HodgeLean.Foundations.Program.SchoenTransferQ3PointCoclassRestriction

/-! Actual finite normal slices compute the ambient supported pullback coefficient. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular AlgebraicGeometry.SingularCycles HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual commuting finite flat slice and its normal-coordinate
inclusions compute the ambient supported pullback with the full fibre length. -/
theorem s4_q3_ambient_finite_flat_slice_comparison
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)
    {P Q : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
    [Smooth P.hom] [Smooth Q.hom]
    [T1Space (ComplexPoint P)] [T1Space (ComplexPoint Q)]
    (f : P ⟶ Q) [IsFinite f.left] [Flat f.left]
    (q : C(M, N)) (jX : C(ComplexPoint P, M)) (jZ : C(ComplexPoint Q, N))
    (hsquare : ∀ y, q (jX y) = jZ (Point.map f y))
    (S : Set M) (T : Set N) (hST : ∀ y, q y ∈ T → y ∈ S)
    (eX : OpenPartialHomeomorph M (E × (Fin k → ℂ)))
    (eZ : OpenPartialHomeomorph N (F × (Fin k → ℂ)))
    (hSX : ∀ y ∈ eX.source, y ∈ S ↔ (eX y).2 = 0)
    (hTZ : ∀ y ∈ eZ.source, y ∈ T ↔ (eZ y).2 = 0)
    (sX : OpenPartialHomeomorph (ComplexPoint P) ((Fin 0 → ℂ) × (Fin k → ℂ)))
    (sZ : OpenPartialHomeomorph (ComplexPoint Q) ((Fin 0 → ℂ) × (Fin k → ℂ)))
    (hsX : a3b4_IsHolChart P.hom sX) (hsZ : a3b4_IsHolChart Q.hom sZ)
    (x : ComplexPoint P) (hx : x ∈ sX.source) (hz : Point.map f x ∈ sZ.source)
    (hx0 : sX x = 0) (hz0 : sZ (Point.map f x) = 0)
    (hxe : jX x ∈ eX.source) (hxe0 : (eX (jX x)).2 = 0)
    (VZ : Set N) (hVZ : VZ ⊆ eZ.source)
    (hqV : ∀ y ∈ flattenedSupportNeighborhood E k eX (jX x) hxe, q y ∈ VZ)
    (hjX : ∀ y ∈ flattenedSupportNeighborhood (Fin 0 → ℂ) k sX x hx,
      jX y ∈ flattenedSupportNeighborhood E k eX (jX x) hxe)
    (hjZ : ∀ y ∈ flattenedSupportNeighborhood (Fin 0 → ℂ) k sZ (Point.map f x) hz,
      jZ y ∈ VZ)
    (hfV : ∀ y ∈ flattenedSupportNeighborhood (Fin 0 → ℂ) k sX x hx,
      Point.map f y ∈ flattenedSupportNeighborhood (Fin 0 → ℂ) k sZ (Point.map f x) hz)
    (hnX : ∀ y ∈ flattenedSupportNeighborhood (Fin 0 → ℂ) k sX x hx,
      (eX (jX y)).2 = (sX y).2)
    (hnZ : ∀ y ∈ flattenedSupportNeighborhood (Fin 0 → ℂ) k sZ (Point.map f x) hz,
      (eZ (jZ y)).2 = (sZ y).2)
    (α : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of N) Tᶜ) (2 * k))
    (a : ℚ)
    (hα : relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap VZ T) α =
      a • chartNormalProjectionCoclass F k eZ T hTZ VZ hVZ) :
    relativeCohomologyMap ℚ (2 * k)
      (a3b4_neighborhoodPairMap
        (flattenedSupportNeighborhood E k eX (jX x) hxe) S)
      (relativeCohomologyMap ℚ (2 * k)
        (a3b4_supportPairMap (TopCat.ofHom q) S T hST) α) =
      (a * ((pointFibreLength f.left x.underlying).toNat : ℚ)) •
        chartNormalProjectionCoclass E k eX S hSX
          (flattenedSupportNeighborhood E k eX (jX x) hxe)
          (flattenedSupportNeighborhood_subset_source E k eX (jX x) hxe) := by
  let NX := flattenedSupportNeighborhood E k eX (jX x) hxe
  let NS := flattenedSupportNeighborhood (Fin 0 → ℂ) k sX x hx
  let NT := flattenedSupportNeighborhood (Fin 0 → ℂ) k sZ (Point.map f x) hz
  have hNS := flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) k sX x hx
  have hNT := flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) k sZ (Point.map f x) hz
  have hNX := flattenedSupportNeighborhood_subset_source E k eX (jX x) hxe
  have hpointX := s4_q3_zero_tangent_chart_flattens_point k sX x hx hx0
  have hpointZ := s4_q3_zero_tangent_chart_flattens_point k sZ (Point.map f x) hz hz0
  have hxNS : x ∈ NS := mem_flattenedSupportNeighborhood (Fin 0 → ℂ) k sX x hx
  have hzNT : Point.map f x ∈ NT :=
    mem_flattenedSupportNeighborhood (Fin 0 → ℂ) k sZ (Point.map f x) hz
  have hzT : jZ (Point.map f x) ∈ T := by
    apply (hTZ _ (hVZ (hjZ _ hzNT))).mpr
    rw [hnZ _ hzNT]
    exact congrArg Prod.snd hz0
  have hisol : ∀ y ∈ NS, Point.map f y = Point.map f x → y = x := by
    intro y hy hfy
    apply Set.mem_singleton_iff.mp
    apply (hpointX y (hNS hy)).mpr
    rw [← hnX y hy]
    apply (hSX _ (hNX (hjX y hy))).mp
    apply hST
    rw [hsquare y, hfy]
    exact hzT
  let qN := s4_q3_neighbourhood_support_map q S T NX VZ hqV (fun y _ => hST y)
  let JX := s4_q3_slice_neighbourhood_pair_map eX sX S {x} hSX hpointX jX
    NS NX hNS hNX hjX hnX
  let JZ := s4_q3_slice_neighbourhood_pair_map eZ sZ T {Point.map f x} hTZ hpointZ jZ
    NT VZ hNT hVZ hjZ hnZ
  let fN := s4_q3_neighbourhood_support_map (Point.continuousMap f) {x} {Point.map f x}
    NS NT hfV (fun y hy hfy => hisol y hy hfy)
  let t := neighborhoodPointComplementPairMap (NT : Set (ComplexPoint Q)) (Point.map f x)
  let ω := normalizedRelativeCoclass
    (localClassOfChart k (pointChart sZ) (Point.map f x) ⟨hz, Set.mem_univ _⟩)
    (s4_q3_centred_point_class_ne_zero k sZ (Point.map f x) hz hz0)
  let ν := chartNormalProjectionCoclass E k eX S hSX NX hNX
  let η := chartNormalProjectionCoclass (Fin 0 → ℂ) k sX {x} hpointX NS hNS
  have hnorm : relativeCohomologyMap ℚ (2 * k) JX ν = η :=
    s4_q3_slice_neighbourhood_pair_map_normal_coclass E (Fin 0 → ℂ) k
      eX sX S {x} hSX hpointX jX NS NX hNS hNX hjX hnX
  have hinj : Function.Injective (relativeCohomologyMap ℚ (2 * k) JX) :=
    s4_q3_small_normal_slice_pullback_injective E (Fin 0 → ℂ) k eX sX S {x}
      hSX hpointX (jX x) hxe hxe0 NS hNS NS.isOpen x hxNS (congrArg Prod.snd hx0)
      JX (fun y => hnX y.1 y.2)
  have hsq : JX ≫ qN = fN ≫ JZ := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext y
      apply Subtype.ext
      apply Subtype.ext
      exact hsquare y.1.1
    · ext y
      apply Subtype.ext
      exact hsquare y.1
  have htarget : relativeCohomologyMap ℚ (2 * k) JZ
      (relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap VZ T) α) =
      a • relativeCohomologyMap ℚ (2 * k) t ω := by
    rw [hα, map_smul]
    have hnormalZ := s4_q3_slice_neighbourhood_pair_map_normal_coclass F (Fin 0 → ℂ) k
      eZ sZ T {Point.map f x} hTZ hpointZ jZ NT VZ hNT hVZ hjZ hnZ
    change _ = a • relativeCohomologyMap ℚ (2 * k) t ω
    rw [hnormalZ]
    congr 1
    exact (s4_q3_point_coclass_restrict_to_normal k sZ (Point.map f x) hz hz0).symm
  letI : IsLocallyNoetherian Q.left := LocallyOfFiniteType.isLocallyNoetherian Q.hom
  letI : CompactSpace Q.left := QuasiCompact.compactSpace_of_compactSpace Q.hom
  letI : IsNoetherian Q.left := {}
  obtain ⟨y, hy, hcomp⟩ := s4_q3_finite_point_inverse_component f x
  have hdegree : relativeCohomologyMap ℚ (2 * k) (fN ≫ t) ω =
      ((pointFibreLength f.left x.underlying).toNat : ℚ) • η := by
    have hpair : fN ≫ t = isolatedPairMap (TopCat.ofHom (Point.continuousMap f)) NS x hisol := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl
    rw [hpair]
    exact s4_q3_finite_flat_slice_normal_coclass f k x sX sZ hsX hsZ hx hz hx0 hz0
      hisol y hy (ccm3_genericLength_finite_pos f _ y hcomp).2
  have hcoef := s4_q3_slice_square_normal_coefficient (2 * k) qN JX fN JZ t hsq hinj
    (relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap VZ T) α) ω ν η a
    ((pointFibreLength f.left x.underlying).toNat : ℚ) htarget hdegree hnorm
  have hrestrict := congrArg (fun φ => relativeCohomologyMap ℚ (2 * k) φ α)
    (s4_q3_neighbourhood_support_map_ambient q S T NX VZ hqV hST).symm
  rw [relativeCohomologyMap_comp, relativeCohomologyMap_comp,
    LinearMap.comp_apply, LinearMap.comp_apply] at hrestrict
  exact hrestrict.trans hcoef

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenSmoothOrientation
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectivePointedBoundaryProjection
import HodgeLean.Foundations.QuotientDuality.ProperCycleChartLocalScalar
import HodgeLean.Foundations.QuotientDuality.ProperCycleCompactManifoldPointDetection
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.LocalOrientationNeighborhood

/-! # Actual ordinary top class lifts from a compact smooth-open support -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Analytic HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

/-- The canonical orientation along the actual compact complement of a boundary neighborhood lifts to an original ordinary class through the specified original bijective relative projection.
Source: j5c_hasClassAlong_of_isCompact; properCycle_image_projected_support_point_value.
HC no distance; AV milestone no distance. -/
theorem properCycle_smooth_open_compact_top_class_lift
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (U : X.left.Opens)
    [LocallyOfFiniteType (openScheme X U).hom] [QuasiCompact (openScheme X U).hom]
    [IsSeparated (openScheme X U).hom] (d : ℕ)
    [SmoothOfRelativeDimension d (openScheme X U).hom]
    (N : Set (ComplexPoint X)) (hN : IsOpen N)
    (hcover : ∀ x : ComplexPoint X, x ∉ N → x ∈ Set.range (Point.map (openInclusion X U)))
    (hproj : Function.Bijective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := a3b4_an X.hom) N) (2*d)).hom) :
    ∃ c : Homology ℚ (a3b4_an X.hom) (2*d),
      ∀ y : ComplexPoint (openScheme X U), Point.map (openInclusion X U) y ∉ N →
        localOrientation (a3b4_an X.hom) (2*d) c (Point.map (openInclusion X U) y) =
          properCycle_open_smooth_orientation X U d y := by
  let Y := openScheme X U
  letI : T2Space (ComplexPoint Y) := f4_t2Space Y
  let f := TopCat.ofHom (Point.continuousMap (openInclusion X U))
  have hf : Topology.IsOpenEmbedding f := ComplexPoint.isOpenEmbedding_map_open X U
  let K : Set (ComplexPoint X) := Nᶜ
  let A : Set (ComplexPoint Y) := f ⁻¹' K
  have hK : IsCompact K := hN.isClosed_compl.isCompact
  have hcoverK : K ⊆ Set.range f := hcover
  have himage : f '' A = K := Set.image_preimage_eq_of_subset hcoverK
  have hA : IsCompact A := hf.isEmbedding.isCompact_iff.mpr (by rw [himage]; exact hK)
  have hn : Module.finrank ℝ (Fin d → ℂ) = 2*d := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  obtain ⟨a, ha⟩ := j5c_hasClassAlong_of_isCompact (M := ComplexPoint Y) (E := Fin d → ℂ)
    hn (complexLocalOrientation Y d) (exists_neighborhood_complexLocalOrientation Y d) hA
  have hsupport : (f '' A)ᶜ = N := by
    rw [himage]
    exact compl_compl N
  have hproj' : Function.Bijective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := a3b4_an X.hom) (f '' A)ᶜ) (2*d)).hom := by
    rw [hsupport]
    exact hproj
  obtain ⟨c, hc⟩ := hproj'.surjective
    (relativeHomologyMap ℚ (2*d) (imageSupportPairMap f hf.injective A) a)
  refine ⟨c, ?_⟩
  intro y hy
  have hyA : y ∈ A := hy
  have hp := properCycle_image_projected_support_point_value f hf.injective A (2*d) c a hc.symm y hyA
  rw [ha y hyA] at hp
  exact hp.symm

/-- The actual compact smooth-open point values detect an original ordinary class through its original injective relative projection.
Source: properCycle_compact_manifold_support_point_detection; Set.image_preimage_eq_of_subset.
HC no distance; AV milestone no distance. -/
theorem properCycle_smooth_open_compact_top_class_detection
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (U : X.left.Opens)
    [LocallyOfFiniteType (openScheme X U).hom] [QuasiCompact (openScheme X U).hom]
    [IsSeparated (openScheme X U).hom] (d : ℕ)
    [SmoothOfRelativeDimension d (openScheme X U).hom]
    (N : Set (ComplexPoint X)) (hN : IsOpen N)
    (hcover : ∀ x : ComplexPoint X, x ∉ N → x ∈ Set.range (Point.map (openInclusion X U)))
    (hproj : Function.Injective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := a3b4_an X.hom) N) (2*d)).hom)
    (c : Homology ℚ (a3b4_an X.hom) (2*d))
    (hc : ∀ y : ComplexPoint (openScheme X U), Point.map (openInclusion X U) y ∉ N →
      localOrientation (a3b4_an X.hom) (2*d) c (Point.map (openInclusion X U) y) = 0) : c = 0 := by
  let Y := openScheme X U
  letI : T2Space (a3b4_an X.hom) := f4_t2Space X
  letI : T2Space (ComplexPoint Y) := f4_t2Space Y
  let f := TopCat.ofHom (Point.continuousMap (openInclusion X U))
  have hf : Topology.IsOpenEmbedding f := ComplexPoint.isOpenEmbedding_map_open X U
  let K : Set (ComplexPoint X) := Nᶜ
  let A : Set (ComplexPoint Y) := f ⁻¹' K
  have hK : IsCompact K := hN.isClosed_compl.isCompact
  have hcoverK : K ⊆ Set.range f := hcover
  have himage : f '' A = K := Set.image_preimage_eq_of_subset hcoverK
  have hA : IsCompact A := hf.isEmbedding.isCompact_iff.mpr (by rw [himage]; exact hK)
  have hn : Module.finrank ℝ (Fin d → ℂ) = 2*d := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hsupport : (f '' A)ᶜ = N := by
    rw [himage]
    exact compl_compl N
  have hproj' : Function.Injective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := a3b4_an X.hom) (f '' A)ᶜ) (2*d)).hom := by
    rw [hsupport]
    exact hproj
  exact properCycle_compact_manifold_support_point_detection (E := Fin d → ℂ)
    (a3b4_an X.hom) (TopCat.of (ComplexPoint Y)) f hf A hA (2*d) hn hproj' c hc

end HodgeLean.Foundations.QuotientDuality

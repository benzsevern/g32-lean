import HodgeLean.Foundations.QuotientDuality.PersistenceAmbientPairComparison
import HodgeLean.Foundations.QuotientDuality.PersistenceFiniteCoverCollapseComparison
import HodgeLean.Foundations.QuotientDuality.PersistenceEmptyPreimage
import HodgeLean.Foundations.QuotientDuality.PersistenceSupport

/-! Actual original-pair comparison for finite covers of projective bases. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_finite_cover_pair_relative_cohomology_bijective
    (K : Type) [Field K] [Algebra ℚ K]
    (X Y BX BY E : Over (Spec ↧ℂ)) [IsProjective BX.hom] [IsProjective BY.hom]
    (βX : X ⟶ BX) [IsFinite βX.left] (βY : Y ⟶ BY) [IsFinite βY.left]
    (j : E ⟶ Y) [IsClosedImmersion j.left] (f : X ⟶ Y)
    (hclosed : IsClosedMap (Point.map f))
    (hfibre : ∀ y, y ∉ Set.range (Point.map j) → ∃! x, Point.map f x = y)
    (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n
      (persistencePairMap (TopCat.ofHom (Point.continuousMap f))
        (Set.range (Point.map j)))) := by
  classical
  let A := Set.range (Point.map j)
  have hA : IsClosed A := isClosed_range_map_of_closedImmersion j
  by_cases hempty : Point.map f ⁻¹' A = ∅
  · exact persistence_empty_preimage_relative_cohomology_bijective K
      (Point.continuousMap f) hclosed A hA hfibre hempty n
  · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    haveI : IsClosedImmersion (pullback.fst f j).left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (((IsPullback.of_hasPullback f j).map (Over.forget _)).flip)
        (inferInstance : IsClosedImmersion j.left)
    have hsource := persistence_finite_cover_closed_locus_ambient_deformation
      X BX (pullback f j) βX (pullback.fst f j)
    rw [persistence_pullback_point_range f j] at hsource
    obtain ⟨PX, hPX, hBPX, rX, HX, hfixedX, hretX⟩ := hsource
    obtain ⟨PY, hPY, hAPY, rY, HY, hfixedY, hretY⟩ :=
      persistence_finite_cover_closed_locus_ambient_deformation Y BY E βY j
    exact persistence_ambient_pair_relative_cohomology_bijective K
      (Point.continuousMap f) hclosed A hA hfibre x hx
      PX hPX hBPX rX HX hfixedX hretX PY hPY hAPY rY HY hfixedY hretY n

end HodgeLean.Foundations.QuotientDuality

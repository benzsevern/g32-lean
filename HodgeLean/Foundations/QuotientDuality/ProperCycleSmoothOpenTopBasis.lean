import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothOpenCompactLift
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothOpenScalar

/-! # Original top homology bases normalized on an actual smooth algebraic open -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual compact smooth-open orientation lift and the original injective boundary projection give an original ordinary top homology basis normalized on the whole connected smooth algebraic open.
Source: properCycle_smooth_open_compact_top_class_lift; properCycle_smooth_open_top_class_scalar; properCycle_smooth_open_compact_top_class_detection.
HC no distance; AV milestone no distance. -/
theorem properCycle_smooth_open_normalized_top_basis
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (U : X.left.Opens)
    [IsIntegral (openScheme X U).left] [Smooth (openScheme X U).hom]
    [QuasiCompact (openScheme X U).hom] [IsSeparated (openScheme X U).hom]
    (d : ℕ) [SmoothOfRelativeDimension d (openScheme X U).hom]
    (N : Set (ComplexPoint X)) (hN : IsOpen N)
    (hcover : ∀ x : ComplexPoint X, x ∉ N → x ∈ Set.range (Point.map (openInclusion X U)))
    (hproj : Function.Bijective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := a3b4_an X.hom) N) (2*d)).hom)
    (y₀ : ComplexPoint (openScheme X U)) (hy₀ : Point.map (openInclusion X U) y₀ ∉ N) :
    ∃ c : Homology ℚ (a3b4_an X.hom) (2*d),
      (∀ y : ComplexPoint (openScheme X U),
        localOrientation (a3b4_an X.hom) (2*d) c (Point.map (openInclusion X U) y) =
          properCycle_open_smooth_orientation X U d y) ∧
      Function.Bijective (LinearMap.toSpanSingleton ℚ
        (Homology ℚ (a3b4_an X.hom) (2*d)) c) := by
  obtain ⟨c, hc⟩ := properCycle_smooth_open_compact_top_class_lift X U d N hN hcover hproj
  have hμ : properCycle_open_smooth_orientation X U d y₀ ≠ 0 := by
    intro hz
    have hh : (1 : ℚ) = 0 := (properCycle_open_smooth_orientation_generates X U d y₀).injective
      (by
        change (1 : ℚ) • properCycle_open_smooth_orientation X U d y₀ =
          (0 : ℚ) • properCycle_open_smooth_orientation X U d y₀
        rw [hz]
        simp)
    exact one_ne_zero hh
  obtain ⟨q₀, hq₀⟩ := properCycle_smooth_open_top_class_scalar X U d c
  have hq₀one : q₀ = 1 := smul_left_injective ℚ hμ (by
    have h := hq₀ y₀
    rw [hc y₀ hy₀] at h
    simpa only [one_smul] using h.symm)
  have hnorm (y : ComplexPoint (openScheme X U)) :
      localOrientation (a3b4_an X.hom) (2*d) c (Point.map (openInclusion X U) y) =
        properCycle_open_smooth_orientation X U d y := by
    rw [hq₀ y, hq₀one, one_smul]
  have hspan (b : Homology ℚ (a3b4_an X.hom) (2*d)) : ∃ q : ℚ, q • c = b := by
    obtain ⟨q, hq⟩ := properCycle_smooth_open_top_class_scalar X U d b
    have hz : b - q • c = 0 := properCycle_smooth_open_compact_top_class_detection
      X U d N hN hcover hproj.injective (b - q • c) (by
        intro y hy
        change (relativeHomologyProjection ℚ
          (pointComplementPair (Point.map (openInclusion X U) y)) (2*d)).hom (b - q • c) = 0
        rw [map_sub, map_smul]
        change localOrientation (a3b4_an X.hom) (2*d) b _ -
          q • localOrientation (a3b4_an X.hom) (2*d) c _ = 0
        rw [hq y, hnorm y, sub_self])
    exact ⟨q, (sub_eq_zero.mp hz).symm⟩
  have hc0 : c ≠ 0 := by
    intro hz
    have h := hnorm y₀
    simp only [hz, localOrientation, map_zero] at h
    exact hμ h.symm
  exact ⟨c, hnorm, ⟨fun q r h => smul_left_injective ℚ hc0 h, hspan⟩⟩

end HodgeLean.Foundations.QuotientDuality

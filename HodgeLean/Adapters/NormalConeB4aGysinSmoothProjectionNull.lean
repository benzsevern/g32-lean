import HodgeLean.Adapters.NormalConeB4aGysinComplexLowerDimension
import HodgeLean.Adapters.NormalConeB4aGysinSmoothSourceCover

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- The parameter projection of a lower-dimensional smooth scheme source has
zero volume in any supplied holomorphic ambient chart. -/
theorem a3b4a_gysin_smooth_source_parameter_image_null
    (X Y : Over (Spec (CommRingCat.of ℂ))) (m n c : ℕ)
    [SmoothOfRelativeDimension m X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) (hmn : m < n) :
    MeasureTheory.volume ((fun x => (Φ (Point.map f x)).1) ''
      (Point.map f ⁻¹' Φ.source)) = 0 := by
  obtain ⟨J, hJ, hcover⟩ := a3b4a_gysin_smooth_source_countable_image_cover X Y m n c f Φ
  let η : ComplexPoint X → (Fin m → ℂ) → ((Fin n → ℂ) × (Fin c → ℂ)) :=
    fun j a => Φ (Point.map f ((chartAt (Fin m → ℂ) j).symm a))
  let Ω : ComplexPoint X → Set (Fin m → ℂ) := fun j =>
    (chartAt (Fin m → ℂ) j).target ∩
      (chartAt (Fin m → ℂ) j).symm ⁻¹' (Point.map f ⁻¹' Φ.source)
  have hproj : (fun x => (Φ (Point.map f x)).1) '' (Point.map f ⁻¹' Φ.source) =
      ⋃ j ∈ J, (fun a => (η j a).1) '' Ω j := by
    have h := congrArg (fun T : Set ((Fin n → ℂ) × (Fin c → ℂ)) => Prod.fst '' T) hcover
    simpa only [Set.image_image, Set.image_iUnion, Function.comp_def] using h
  rw [hproj]
  apply (MeasureTheory.measure_biUnion_null_iff hJ).mpr
  intro j _
  apply a3b4a_gysin_complex_lower_dimensional_image_null (Ω j) (fun a => (η j a).1) ?_ hmn
  intro a ha
  exact ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin c → ℂ)).analyticAt (η j a)).comp
    (a3b4a_gysin_smooth_source_coordinate_parametrization X Y m n c f Φ hΦ j a ha)

end HodgeLean.Adapters

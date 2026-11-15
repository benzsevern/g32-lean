import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateInclusion

/-! # Actual affine charts of the standard projective coordinate inclusion -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A retained homogeneous variable is unchanged by coordinate elimination. -/
theorem paired_c3_coordinate_projection_variable {A ι κ : Type} [CommRing A]
    (e : κ ↪ ι) (i : κ) :
    pairedC3GradedCoordinateProjection (A := A) e (X (e i)) = X i := by
  have h := paired_c3_graded_coordinate_retraction (A := A) e (X i)
  change pairedC3GradedCoordinateProjection (A := A) e (MvPolynomial.rename e (X i)) = X i at h
  simpa only [MvPolynomial.rename_X] using h

/-- Every discarded homogeneous variable vanishes under elimination. -/
theorem paired_c3_coordinate_projection_variable_zero {A ι κ : Type} [CommRing A]
    (e : κ ↪ ι) (j : ι) (hj : j ∉ Set.range e) :
    pairedC3GradedCoordinateProjection (A := A) e (X j) = 0 := by
  classical
  change MvPolynomial.killCompl (R := A) e.injective (X j) = 0
  simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X, dite_eq_right hj]

/-- The actual normal coordinate on an affine chart is the homogeneous
ratio with the retained denominator. -/
def pairedC3CoordinateNormalRatio {A ι κ : Type} [CommRing A]
    (e : κ ↪ ι) (i : κ) (j : ι) :
    Away (homogeneousSubmodule ι A) (X (e i)) :=
  Away.mk _ (isHomogeneous_X A (e i)) 1 (X j) (by simpa using isHomogeneous_X A j)

/-- The discarded-coordinate ratio belongs to the actual affine chart
kernel, with the original numerator and denominator. -/
theorem paired_c3_coordinate_normal_ratio_vanishes {A ι κ : Type} [CommRing A]
    (e : κ ↪ ι) (i : κ) (j : ι) (hj : j ∉ Set.range e) :
    Away.map (pairedC3GradedCoordinateProjection (A := A) e) (X (e i))
      (pairedC3CoordinateNormalRatio e i j) = 0 := by
  unfold pairedC3CoordinateNormalRatio
  rw [Away.map_mk]
  apply HomogeneousLocalization.mk_eq_zero_of_num
  apply Subtype.ext
  exact paired_c3_coordinate_projection_variable_zero (A := A) e j hj

/-- The inverse image of a retained target chart is its original source chart. -/
theorem paired_c3_coordinate_inclusion_preimage_basicOpen {A ι κ : Type} [CommRing A]
    (e : κ ↪ ι) (i : κ) :
    pairedC3PolynomialCoordinateInclusion (A := A) e ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule ι A) (X (e i)) =
    Proj.basicOpen (homogeneousSubmodule κ A) (X i) := by
  rw [pairedC3PolynomialCoordinateInclusion, Proj.map_preimage_basicOpen,
    paired_c3_coordinate_projection_variable]

/-- Each projective coordinate-inclusion chart is the actual affine
map of homogeneous degree-zero localizations, in a cartesian square. -/
theorem paired_c3_coordinate_inclusion_chart_isPullback
    {A ι κ : Type} [CommRing A] (e : κ ↪ ι) (i : κ) :
    let f := pairedC3GradedCoordinateProjection (A := A) e
    IsPullback
      (Spec.map (CommRingCat.ofHom (Away.map f (X (e i)))))
      (Proj.awayι (homogeneousSubmodule κ A) (f (X (e i)))
        (f.map_mem (isHomogeneous_X A (e i))) zero_lt_one)
      (Proj.awayι (homogeneousSubmodule ι A) (X (e i))
        (isHomogeneous_X A (e i)) zero_lt_one)
      (pairedC3PolynomialCoordinateInclusion (A := A) e) := by
  dsimp only
  let f := pairedC3GradedCoordinateProjection (A := A) e
  let a := Proj.awayι (homogeneousSubmodule ι A) (X (e i))
    (isHomogeneous_X A (e i)) zero_lt_one
  let b := Proj.awayι (homogeneousSubmodule κ A) (f (X (e i)))
    (f.map_mem (isHomogeneous_X A (e i))) zero_lt_one
  let φ := Spec.map (CommRingCat.ofHom (Away.map f (X (e i))))
  have hw : b ≫ pairedC3PolynomialCoordinateInclusion (A := A) e = φ ≫ a :=
    Proj.awayι_comp_map f _ zero_lt_one (X (e i)) (isHomogeneous_X A (e i))
  have hr : pairedC3PolynomialCoordinateInclusion (A := A) e ⁻¹ᵁ a.opensRange = b.opensRange := by
    simp only [a, b, f, Proj.opensRange_awayι, pairedC3PolynomialCoordinateInclusion,
      Proj.map_preimage_basicOpen]
  exact IsOpenImmersion.isPullback φ b a _ hw hr

/-- The chart comparison is a surjection on the actual affine coordinate rings. -/
theorem paired_c3_coordinate_inclusion_chart_surjective
    {A ι κ : Type} [CommRing A] (e : κ ↪ ι) (i : κ) :
    Function.Surjective (Away.map (pairedC3GradedCoordinateProjection (A := A) e) (X (e i))) :=
  s2e_away_map_surjective_of_graded_retraction _ _
    (pairedC3GradedCoordinateProjection e) (pairedC3GradedCoordinateSection e)
    (paired_c3_graded_coordinate_retraction e) (X (e i)) (isHomogeneous_X A (e i))

end HodgeLean.Foundations.Program.G32Native

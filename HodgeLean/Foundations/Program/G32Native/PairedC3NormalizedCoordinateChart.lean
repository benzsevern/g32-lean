import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateChartMap

/-! # Cartesian projective charts with their literal source denominator -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- Equality of denominators transports the actual affine chart
inclusion, retaining the original morphism into the projective scheme. -/
theorem paired_c3_away_cast_inclusion {A σ : Type} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (G : ℕ → σ) [GradedRing G]
    {x y : A} (h : x = y) {d : ℕ} (hx : x ∈ G d) (hy : y ∈ G d) (hd : 0 < d) :
    Spec.map (RingEquiv.cast (R := fun z => Away G z) h).toCommRingCatIso.hom ≫
      Proj.awayι G x hx hd = Proj.awayι G y hy hd := by
  cases h
  change Spec.map (𝟙 _) ≫ Proj.awayι G x hx hd = Proj.awayι G x hy hd
  rw [Spec.map_id, Category.id_comp]

/-- The normalized projective comparison chart commutes as an equality
of the actual scheme morphisms. -/
theorem paired_c3_normalized_coordinate_chart_commutes {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
        (isHomogeneous_X ℂ i) zero_lt_one ≫ pairedC3PolynomialCoordinateInclusion (A := ℂ) e =
      Spec.map (CommRingCat.ofHom (pairedC3CoordinateChartMap e i)) ≫
        Proj.awayι (homogeneousSubmodule (Fin (n + 1)) ℂ) (X (e i))
          (isHomogeneous_X ℂ (e i)) zero_lt_one := by
  let f := pairedC3GradedCoordinateProjection (A := ℂ) e
  let C := RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z)
    (paired_c3_coordinate_projection_variable (A := ℂ) e i)
  have hb := paired_c3_away_cast_inclusion (homogeneousSubmodule (Fin (k + 1)) ℂ)
    (paired_c3_coordinate_projection_variable (A := ℂ) e i)
    (f.map_mem (isHomogeneous_X ℂ (e i))) (isHomogeneous_X ℂ i) zero_lt_one
  rw [← hb, Category.assoc]
  change _ ≫ (_ ≫ Proj.map f _) = _
  rw [Proj.awayι_comp_map f _ zero_lt_one (X (e i)) (isHomogeneous_X ℂ (e i))]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The normalized affine comparison gives the original cartesian
restriction of the projective coordinate immersion. -/
theorem paired_c3_normalized_coordinate_chart_isPullback {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (pairedC3CoordinateChartMap e i)))
      (Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
        (isHomogeneous_X ℂ i) zero_lt_one)
      (Proj.awayι (homogeneousSubmodule (Fin (n + 1)) ℂ) (X (e i))
        (isHomogeneous_X ℂ (e i)) zero_lt_one)
      (pairedC3PolynomialCoordinateInclusion (A := ℂ) e) := by
  apply IsOpenImmersion.isPullback
  · exact paired_c3_normalized_coordinate_chart_commutes e i
  · rw [Proj.opensRange_awayι, Proj.opensRange_awayι,
      paired_c3_coordinate_inclusion_preimage_basicOpen]

end HodgeLean.Foundations.Program.G32Native

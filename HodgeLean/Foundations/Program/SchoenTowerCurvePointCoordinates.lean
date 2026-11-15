import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- An affine coordinate neighborhood of a point of a smooth integral complex curve.
Source: Stacks Project, Tag 054L; `nonempty_localEtaleCoordinates`. -/
theorem s2t_curve_point_coordinates (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (hdim : TopologicalSpace.dim X.left = 1) (x : X.left) :
    ∃ (U : X.left.affineOpens)
      (f : Over.mk (U.1.ι ≫ X.hom) ⟶
        Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)),
      x ∈ U.1 ∧ Etale f.left := by
  letI : SmoothOfRelativeDimension 1 X.hom := by
    rw [← hdim]
    infer_instance
  let D := localEtaleCoordinates X 1 x
  letI : IsAffine D.neighborhood.toScheme := D.isAffine
  letI : Etale (Spec.map (CommRingCat.ofHom D.coordinateRingHomOnOpen)) :=
    HasRingHomProperty.Spec_iff.mpr D.coordinateRingHomOnOpen_etale
  refine ⟨⟨D.neighborhood, D.isAffine⟩, D.toAffineSpaceOver, D.mem, ?_⟩
  change Etale D.toAffineSpace
  dsimp only [LocalEtaleCoordinates.toAffineSpace]
  haveI : IsIso D.neighborhood.toScheme.toSpecΓ := inferInstance
  have h₁ : Etale D.neighborhood.toScheme.toSpecΓ := inferInstance
  haveI : Etale (AffineSpace.SpecIso (Fin 1) ↧ℂ).inv := inferInstance
  have h₂ : Etale (Spec.map (CommRingCat.ofHom D.coordinateRingHomOnOpen) ≫
      (AffineSpace.SpecIso (Fin 1) ↧ℂ).inv) := Etale.etale_comp
        (Spec.map (CommRingCat.ofHom D.coordinateRingHomOnOpen))
        (AffineSpace.SpecIso (Fin 1) ↧ℂ).inv
  exact @Etale.etale_comp _ _ _ _ _ h₁ h₂

/-- The finite-support coordinate conclusion for a support with at most one element.
Source: Stacks Project, Tag 054L; injectivity of an open immersion on complex points. -/
theorem s2t_curve_subsingleton_coordinates (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (hdim : TopologicalSpace.dim X.left = 1) (s : Finset (ComplexPoint X))
    (hs : (s : Set (ComplexPoint X)).Subsingleton) :
    ∃ (U : X.left.affineOpens)
      (f : Over.mk (U.1.ι ≫ X.hom) ⟶
        Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)),
      (∀ x ∈ s, Set.range x.left ⊆ U.1) ∧ Etale f.left ∧
      ∀ (x y : ComplexPoint (Over.mk (U.1.ι ≫ X.hom))),
        Point.map (Over.homMk U.1.ι) x ∈ s →
        Point.map (Over.homMk U.1.ι) y ∈ s →
        Point.map f x = Point.map f y → x = y := by
  classical
  have hext (U : X.left.affineOpens)
      (x y : ComplexPoint (Over.mk (U.1.ι ≫ X.hom)))
      (hx : Point.map (Over.homMk U.1.ι) x ∈ s)
      (hy : Point.map (Over.homMk U.1.ι) y ∈ s) : x = y := by
    exact (cancel_mono (show Over.mk (U.1.ι ≫ X.hom) ⟶ X from
      Over.homMk U.1.ι)).mp (hs hx hy)
  by_cases hne : s.Nonempty
  · obtain ⟨p, hp⟩ := hne
    obtain ⟨U, f, hU, hf⟩ := s2t_curve_point_coordinates X hdim p.underlying
    refine ⟨U, f, ?_, hf, fun x y hx hy _ => hext U x y hx hy⟩
    intro q hq
    have hqp : q = p := hs hq hp
    subst q
    simpa only [Scheme.Opens.range_ι] using point_range_subset X U.1 p hU
  · obtain ⟨x⟩ : Nonempty X.left := inferInstance
    obtain ⟨U, f, _, hf⟩ := s2t_curve_point_coordinates X hdim x
    exact ⟨U, f, fun p hp => (hne ⟨p, hp⟩).elim, hf,
      fun x y hx hy _ => hext U x y hx hy⟩

end HodgeLean.Foundations.Program

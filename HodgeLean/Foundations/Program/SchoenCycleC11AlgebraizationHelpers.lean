import HodgeLean.Foundations.Program.SchoenCycleC11ComponentHelpersHi
import HodgeLean.Foundations.Program.SchoenCycleC11SchemeHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11EtaleSmoothHelpers

/-! # Algebraization through actual smooth components
Analytic clopen images determine algebraic opens and their inverse scheme maps.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A finite scheme over projective space is noetherian.
Source: Hartshorne, Algebraic Geometry, II.3; Mathlib, finite type over a noetherian base. -/
theorem s2e_c11_finite_over_projective_noetherian
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (f : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite f.left] : IsNoetherian W.left := by
  have : LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) := inferInstance
  have : LocallyOfFiniteType W.hom := by
    rw [← Over.w f]
    change LocallyOfFiniteType (f.left ≫ ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    infer_instance
  have : CompactSpace (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).left :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace f.left
  exact { __ := LocallyOfFiniteType.isLocallyNoetherian W.hom }

/-- The source of a finite etale morphism to projective space is smooth over the complex numbers.
Source: Mathlib, composition of smooth relative dimensions; projective smoothness. -/
theorem s2e_c11_projective_finite_etale_source_smooth
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (f : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite f.left] [Etale f.left] : Smooth W.hom := by
  have : SmoothOfRelativeDimension k
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
    s0_complex_projective_relative_dimension k
  have : SmoothOfRelativeDimension k W.hom := s2e_c11_etale_smooth_relative_dimension k W _ f
  exact SmoothOfRelativeDimension.smooth k W.hom

/-- A section with analytic clopen image algebraizes on a smooth noetherian finite etale source.
Source: Hartshorne, Algebraic Geometry, Appendix B, component comparison;
SGA 1, Expose I, Proposition 5.1, finite etale degree one. -/
theorem s2e_c11_algebraize_smooth_clopen_section
    (X Y : Over (Spec ↧ℂ)) [Smooth X.hom] [IsNoetherian X.left]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
    (s : Point ℂ Y → Point ℂ X) (hs : ∀ y, Point.map f (s y) = y)
    (himage : IsClopen (Set.range s)) :
    ∃ j : Y ⟶ X, Point.map j = s ∧ j ≫ f = 𝟙 _ := by
  obtain ⟨U, hU, hpoints⟩ := s2e_c11_smooth_analytic_clopen_algebraic X (Set.range s) himage
  exact s2e_c11_section_from_selected_open X Y f s hs U hU hpoints

end HodgeLean.Foundations.Program

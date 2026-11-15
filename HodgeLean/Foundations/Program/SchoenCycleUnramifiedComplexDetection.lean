import HodgeLean.Foundations.Program.SchoenCycleClosedPointDetection
import HodgeLean.Foundations.Program.SchoenCycleSectionEvaluation
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Detection of formal unramifiedness at complex affine neighbourhoods -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Formally unramified section maps on affine neighbourhoods of every complex point detect formal unramifiedness of the actual scheme morphism.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.3 and II.8. -/
theorem s2e_formallyUnramified_of_complex_affine_neighbourhoods
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (f : X ⟶ Y)
    (h : ∀ p : ComplexPoint X, ∃ (U : Y.left.affineOpens) (W : X.left.affineOpens),
      ∃ hp : p.underlying ∈ W.1, ∃ hWU : W.1 ≤ f.left ⁻¹ᵁ U.1,
        (f.left.appLE U.1 W.1 hWU).hom.FormallyUnramified) :
    FormallyUnramified f.left := by
  choose U W hpW hWU hform using h
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hcover : (⨆ p : ComplexPoint X, (W p).1) = ⊤ := by
    apply s2e_open_eq_top_of_contains_closed_points
    intro x hc
    obtain ⟨p, hp⟩ : ∃ p : ComplexPoint X, p.underlying = x :=
      ⟨Over.homMk (pointOfClosedPoint X.hom x hc) (by simp),
        pointOfClosedPoint_apply X.hom x hc _⟩
    subst x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hpW p⟩
  apply (HasRingHomProperty.iff_exists_appLE (P := @FormallyUnramified)
    (RingHom.FormallyUnramified.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.FormallyUnramified.holdsForLocalizationAway).1).mpr
  intro x
  have hx : x ∈ ⨆ p : ComplexPoint X, (W p).1 := by rw [hcover]; trivial
  obtain ⟨p, hxp⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U p, W p, hxp, hWU p, hform p⟩

end HodgeLean.Foundations.Program

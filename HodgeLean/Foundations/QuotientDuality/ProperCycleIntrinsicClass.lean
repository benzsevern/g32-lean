import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicImage
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicExtension

/-! # The specified intrinsic complex top class and its component images

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The uniquely complex-normalized intrinsic top class of an integral projective complex scheme.
Source: Bredon, Sheaf Theory, second edition, V.9; Fulton, Intersection Theory, section 19.1.
HC no distance; AV milestone no distance. -/
def properCycle_intrinsic_class
    (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsProjective V.hom]
    (d : ℕ) (hdim : topologicalKrullDim V.left = (d : ℕ)) :
    Homology ℚ (a3b4_an V.hom) (2 * d) :=
  (properCycle_intrinsic_extension_aux V d hdim).exists.choose

example (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsProjective V.hom]
    (d : ℕ) (hdim : topologicalKrullDim V.left = (d : ℕ)) :
    Homology ℚ (a3b4_an V.hom) (2 * d) := properCycle_intrinsic_class V d hdim

private lemma component_projective
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (ξ : X.left) :
    IsProjective (cycleComponentι X.left ξ ≫ X.hom) := by
  rcases ‹IsProjective X.hom›.nonempty_presentation with ⟨P⟩
  exact ⟨⟨
    { ambientDimension := P.ambientDimension
      immersion := cycleComponentι X.left ξ ≫ P.immersion
      isClosedImmersion := by
        letI := P.isClosedImmersion
        infer_instance
      immersion_toBase := by rw [Category.assoc, P.immersion_toBase] }
  ⟩⟩

/-- A component contributes its intrinsic normalized top class, pushed by its actual reduced closed immersion, in precisely its intrinsic complex dimension.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1.
HC no distance; AV milestone no distance. -/
def properCycle_intrinsic_component
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (d : ℕ) (ξ : X.left) :
    Homology ℚ (a3b4_an X.hom) (2 * d) := by
  let V : Over (Spec ↧ℂ) := Over.mk (cycleComponentι X.left ξ ≫ X.hom)
  letI : IsProjective V.hom := component_projective X ξ
  let f : V ⟶ X := Over.homMk (cycleComponentι X.left ξ) rfl
  exact if hd : topologicalKrullDim V.left = (d : ℕ) then
    properCycle_intrinsic_image f d (properCycle_intrinsic_class V d hd)
    else 0

example (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (d : ℕ) (ξ : X.left)
    (hd : topologicalKrullDim (cycleComponent X.left ξ) ≠ (d : ℕ)) :
    properCycle_intrinsic_component X d ξ = 0 := by
  unfold properCycle_intrinsic_component
  dsimp only
  split_ifs with h
  · exact (hd h).elim
  · rfl

example : properCycle_intrinsic_class ProperCycleSplitChecks.intrinsicPoint 0
    ProperCycleSplitChecks.intrinsicPoint_dimension = ProperCycleSplitChecks.intrinsicPointClass := by
  let H := properCycle_intrinsic_extension_aux ProperCycleSplitChecks.intrinsicPoint 0
    ProperCycleSplitChecks.intrinsicPoint_dimension
  exact H.unique H.exists.choose_spec
    ⟨fun e _ x hx => ProperCycleSplitChecks.intrinsicPointClass_complex e x hx,
      ProperCycleSplitChecks.intrinsicPointClass_generates⟩

example := ProperCycleSplitChecks.intrinsic_component_degree_homology_example

end HodgeLean.Foundations.QuotientDuality

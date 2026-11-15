import HodgeLean.Adapters.NormalConeB4aClassMultiplicity
import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.NormalCoordinates

/-! # Holomorphic restrictions of analytic normal charts

Route: analytic regularity in the smooth complex-point manifold gives
regularity on a neighborhood. Coordinate projections are analytic, and F4's
function comparison identifies these coordinates as holomorphic functions.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Analytic
open scoped Manifold ContDiff

/-- An analytic manifold chart at a point has a smaller source on which its
coordinates satisfy the frozen holomorphic-chart predicate. -/
theorem a3b4a_classLocal_exists_holomorphic_restriction
    (X : Over (Spec (CommRingCat.of ℂ))) (d r c : ℕ)
    [SmoothOfRelativeDimension d X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (x : ComplexPoint X) (hx : x ∈ e.source)
    (he : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, (Fin r → ℂ) × (Fin c → ℂ)) ω e x) :
    ∃ (W : Set (ComplexPoint X)) (hW : IsOpen W), x ∈ W ∧
      a3b4_IsHolChart X.hom (e.restrOpen W hW) := by
  obtain ⟨U, hUx, hU⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp he
  obtain ⟨W, hWU, hWo, hxW⟩ := mem_nhds_iff.mp hUx
  have hreg : ContMDiffOn 𝓘(ℂ, Fin d → ℂ)
      𝓘(ℂ, (Fin r → ℂ) × (Fin c → ℂ)) ω e (e.restrOpen W hWo).source :=
    hU.mono (fun y hy => hWU hy.2)
  refine ⟨W, hWo, hxW, ?_⟩
  constructor
  · intro j
    apply (f4_isHolFun_iff_contMDiffOn X d (fun y => (e y).1 j)
      (e.restrOpen W hWo).open_source).mpr
    exact ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℂ (Fin r → ℂ) (Fin c → ℂ))).contMDiff.comp_contMDiffOn hreg
  · intro j
    apply (f4_isHolFun_iff_contMDiffOn X d (fun y => (e y).2 j)
      (e.restrOpen W hWo).open_source).mpr
    exact ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℂ (Fin r → ℂ) (Fin c → ℂ))).contMDiff.comp_contMDiffOn hreg

end HodgeLean.Adapters

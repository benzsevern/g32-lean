import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupConormalSource
import HodgeLean.Foundations.Program.G32Native.PairedResidualPresentationOfIdeal
import HodgeLean.Foundations.Program.G32Native.PairedResidualLastFibre

/-! # A residual presentation from a penultimate conormal and the last ruling -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The penultimate frame and invertible natural total-transform comparison
replace the global flat-pencil input in the residual-presentation consumer.
The residual component still retains its actual smooth curve ruling.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.7.13 and II.8.
The input comparison, frame, residual smoothness and ruling are explicit
geometric data; this construction does not supply them. -/
def pairedLastBlowupPresentation
    {P V : Over (Spec ↧ℂ)} (i : P ⟶ V) [IsClosedImmersion i.left]
    (k : ℕ) (H : Scheme.{0}) (h : H ⟶ P.left)
    (J : V.left.IdealSheafData)
    (hnot : ¬ (i.left.ker.support : Set V.left) ⊆ J.support)
    {Q X : Scheme.{0}} (i₀ : Q ⟶ X) (σ : V.left ⟶ X)
    (p : (residualUnion i J).left ⟶ Q)
    (sq : IsPullback p (residualUnionι i J).left i₀ σ)
    [IsIso (Conormal.comparisonMap i₀ (residualUnionι i J).left σ p sq.w)]
    (e₀ : s2c_conormal i₀ ≅
      (SheafOfModules.free (R := Q.ringCatSheaf) (Fin k) : Q.Modules))
    (C : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 C.hom]
    (c : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) [IsClosedImmersion c.left]
    (g : residualComponent (V := V) J ⟶ C) [Smooth g.left]
    (sq₂ : IsPullback (residualIntersection i J).hom
      (residualIntersectionSecond i J).left c.left g.left)
    (e : (residualIntersection i J).left ≅ H)
    (he : e.hom ≫ h = (residualIntersectionFirst i J).left)
    (hframes : ∀ x : P.left, ∃ U : P.left.Opens, x ∈ U ∧
      Nonempty (Scheme.Modules.restrict (s2c_conormal i.left) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules))) :
    PairedResidualPresentation P V i k
      ((Scheme.Modules.pushforward h).obj (SheafOfModules.unit H.ringCatSheaf)) := by
  letI : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  letI : Smooth (residualComponent (V := V) J).hom := by
    rw [← Over.w g]
    infer_instance
  exact residualPresentationOfIdeal i k _ J hnot
    (paired_last_conormal_source_iso i₀ (residualUnionι i J).left σ p sq.w
      (residualUnionFirst i J).left k e₀)
    (residual_flat_curve_last_iso C c (residualIntersectionSecond i J).left g.left
      (residualIntersection i J).hom sq₂ (residualIntersectionFirst i J).left h e he)
    hframes

#print axioms pairedLastBlowupPresentation

end HodgeLean.Foundations.Program.G32Native

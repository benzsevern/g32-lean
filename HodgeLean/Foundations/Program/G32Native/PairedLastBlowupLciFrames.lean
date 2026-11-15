import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupLocalComparison
import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupConormalSource

/-! # The last total-transform comparison from its lci frames

Only the target's local frames remain to be constructed from the Rees
coordinates. The source frames come from the penultimate global frame.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The penultimate global frame and local lci frames of the total transform
make the natural comparison invertible. No flatness of the blowup is used.
Source: Hartshorne, Algebraic Geometry, II.8, conormal pullback for regular
immersions of unchanged codimension. -/
theorem paired_last_lci_comparison_of_frames
    {Q T V X : Scheme.{0}} (i₀ : Q ⟶ X) (t : T ⟶ V)
    [IsClosedImmersion i₀] [IsClosedImmersion t]
    (σ : V ⟶ X) (p : T ⟶ Q) (sq : CategoryTheory.IsPullback p t i₀ σ)
    (k : ℕ)
    (e₀ : s2c_conormal i₀ ≅
      (SheafOfModules.free (R := Q.ringCatSheaf) (Fin k) : Q.Modules))
    (hT : ∀ x : T, ∃ (U : T.Opens), x ∈ U ∧ IsAffine U.toScheme ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (s2c_conormal t) ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules))) :
    IsIso (Conormal.comparisonMap i₀ t σ p sq.w) := by
  apply paired_conormal_comparison_of_local_frames i₀ t σ p sq
  intro x
  obtain ⟨U, hx, hU, eT⟩ := hT x
  letI : (SheafOfModules.pushforward.{0} p.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward p).IsRightAdjoint
  letI : (SheafOfModules.pushforward.{0} U.ι.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward U.ι).IsRightAdjoint
  let eP := (Scheme.Modules.pullback p).mapIso e₀ ≪≫
    SheafOfModules.pullbackObjFreeIso p.toRingCatSheafHom (Fin k)
  let eU := (Scheme.Modules.pullback U.ι).mapIso eP ≪≫
    SheafOfModules.pullbackObjFreeIso U.ι.toRingCatSheafHom (Fin k)
  exact ⟨U, hx, hU, k, ⟨eU⟩, eT⟩

/-- The actual rank-k lci frames on the total transform supply the free
source used by the residual-presentation consumer on its retained component.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.8. -/
def pairedLastSourceOfLciFrames
    {P Q T V X : Scheme.{0}} (i₀ : Q ⟶ X) (t : T ⟶ V)
    [IsClosedImmersion i₀] [IsClosedImmersion t]
    (σ : V ⟶ X) (p : T ⟶ Q) (sq : CategoryTheory.IsPullback p t i₀ σ)
    (a : P ⟶ T) (k : ℕ)
    (e₀ : s2c_conormal i₀ ≅
      (SheafOfModules.free (R := Q.ringCatSheaf) (Fin k) : Q.Modules))
    (hT : ∀ x : T, ∃ (U : T.Opens), x ∈ U ∧ IsAffine U.toScheme ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (s2c_conormal t) ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules))) :
    (Scheme.Modules.pullback a).obj (s2c_conormal t) ≅
      (SheafOfModules.free (R := P.ringCatSheaf) (Fin k) : P.Modules) := by
  haveI := paired_last_lci_comparison_of_frames i₀ t σ p sq k e₀ hT
  exact paired_last_conormal_source_iso i₀ t σ p sq.w a k e₀

#print axioms paired_last_lci_comparison_of_frames
#print axioms pairedLastSourceOfLciFrames
end HodgeLean.Foundations.Program.G32Native

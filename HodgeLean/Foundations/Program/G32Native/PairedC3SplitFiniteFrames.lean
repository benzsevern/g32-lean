import HodgeLean.Foundations.Program.G32Native.PairedC3SplitFunctorFrame
import HodgeLean.Foundations.Program.G32Native.PairedC3DualInvertible
import HodgeLean.Foundations.Program.G32Native.PairedC3ExtensionLocalFree

/-! # Finite-rank local frames of the actual negative sums -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A specified negative-line frame induces the finite sum-rank frame
under the original scheme pullback. -/
def pairedC3SplitPullbackFrame (k a b : ℕ) {Y : Scheme.{0}} (f : Y ⟶ pairedC3Proj k)
    (e : (Scheme.Modules.pullback f).obj (pairedC3NegativeLine k) ≅
      SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback f).obj (pairedC3SplitBundle k a b) ≅
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin (a + b)) := by
  let F := Scheme.Modules.pullback f
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward f).IsRightAdjoint)
  exact pairedC3SplitFunctorFrame k a F
    (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Fin a)) e b

/-- The negative-sum quotient has finite free local frames of its actual rank.
Source: Hartshorne, Algebraic Geometry, II.5, local triviality of invertible sheaves. -/
theorem paired_c3_split_bundle_finite_frames (k a b : ℕ) (x : pairedC3Proj k) :
    ∃ U : (pairedC3Proj k).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (pairedC3SplitBundle k a b) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin (a + b))) := by
  obtain ⟨U, hx, ⟨e⟩⟩ :=
    (paired_c3_dual_invertible (ProjSpace.isInvertible_twistingSheaf ℂ k)).exists_trivialization x
  exact ⟨U, hx, ⟨pairedC3SplitPullbackFrame k a b U.ι e⟩⟩

#print axioms pairedC3SplitPullbackFrame
#print axioms paired_c3_split_bundle_finite_frames
/-- The arbitrary middle sheaf of the specified split-bundle extension
is locally free; no quasicoherence hypothesis is needed.
Source: Hartshorne, Algebraic Geometry, II.5, local splitting of bundle extensions. -/
theorem paired_c3_split_extension_middle_locallyFree (k a b : ℕ)
    (E : ShortComplex (pairedC3Proj k).Modules) (hE : E.ShortExact)
    (e₁ : E.X₁ ≅ pairedC3SplitBundle k a 0)
    (e₃ : E.X₃ ≅ pairedC3SplitBundle k 0 b) : E.X₂.IsLocallyFree := by
  apply paired_c3_extension_locallyFree_of_frames E hE
  intro x
  obtain ⟨U, hx, ⟨eN⟩⟩ :=
    (paired_c3_dual_invertible (ProjSpace.isInvertible_twistingSheaf ℂ k)).exists_trivialization x
  exact ⟨U, hx, Fin (a + 0), Fin (0 + b), inferInstance,
    ⟨(Scheme.Modules.pullback U.ι).mapIso e₁ ≪≫
      pairedC3SplitPullbackFrame k a 0 U.ι eN⟩,
    ⟨(Scheme.Modules.pullback U.ι).mapIso e₃ ≪≫
      pairedC3SplitPullbackFrame k 0 b U.ι eN⟩⟩

#print axioms paired_c3_split_extension_middle_locallyFree
end HodgeLean.Foundations.Program.G32Native

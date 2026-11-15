import HodgeLean.Foundations.Program.G32Native.PairedC3ExtensionTwist
import HodgeLean.Foundations.Program.G32Native.PairedC3InvertibleDualEvaluation

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- N.4: extensions of negative twisting summands by trivial summands split.
Source: Hartshorne, Algebraic Geometry, III.5.1, H¹ of O(1). -/
theorem paired_c3_route_n_extension_split_aux
    (k a b : ℕ) (hk : 0 < k)
    (T : ShortComplex (pairedC3Proj k).Modules) (hT : T.ShortExact)
    (e₁ : T.X₁ ≅ (SheafOfModules.free (Fin a) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf))
    (e₃ : T.X₃ ≅ pairedC3SplitBundle k 0 b) :
    Nonempty (T.X₂ ≅ pairedC3SplitBundle k (a + 1) b) := by
  exact paired_c3_extension_frame_of_inverse_line k a b T hT e₁ e₃
    (pairedC3NegativePositiveIso k)

end HodgeLean.Foundations.Program.G32Native

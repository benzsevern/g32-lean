import HodgeLean.Foundations.BundleResolution.ChernExtendedExactHelpers
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Union comparisons from actual integer-indexed exact sequences

The right comparison is induced by the actual cokernel. This retains the
chain maps needed for the homology connecting morphism.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace HodgeLean.Foundations.BundleResolution

variable (S T : ShortComplex (CochainComplex (ModuleCat ℚ) ℤ)) (hS : S.ShortExact)
variable (a : S.X₁ ⟶ T.X₁) (b : S.X₂ ⟶ T.X₂) (hab : a ≫ T.f = S.f ≫ b)

def i1_extendedSequenceRightComparison : S.X₃ ⟶ T.X₃ := by
  letI := hS.epi_g
  exact hS.exact.desc (b ≫ T.g) (by
    rw [← Category.assoc, ← hab, Category.assoc, T.zero, comp_zero])

theorem i1_extendedSequenceRightComparison_fac :
    S.g ≫ i1_extendedSequenceRightComparison S T hS a b hab = b ≫ T.g := by
  letI := hS.epi_g
  exact hS.exact.g_desc _ _

def i1_extendedSequenceComparison : S ⟶ T :=
  ShortComplex.homMk a b (i1_extendedSequenceRightComparison S T hS a b hab) hab
    (i1_extendedSequenceRightComparison_fac S T hS a b hab).symm

theorem i1_extendedSequenceComparison_delta (hT : T.ShortExact) (i : ℤ) :
    hS.δ i (i + 1) rfl ≫ homologyMap a (i + 1) =
      homologyMap (i1_extendedSequenceRightComparison S T hS a b hab) i ≫
        hT.δ i (i + 1) rfl :=
  HomologicalComplex.HomologySequence.δ_naturality
    (i1_extendedSequenceComparison S T hS a b hab) hS hT i (i + 1) rfl

theorem i1_extendedSequenceRightComparison_quasiIso (hT : T.ShortExact)
    (ha : QuasiIso a) (hb : QuasiIso b) :
    QuasiIso (i1_extendedSequenceRightComparison S T hS a b hab) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (i1_extendedSequenceComparison S T hS a b hab) hS hT ha hb

end HodgeLean.Foundations.BundleResolution

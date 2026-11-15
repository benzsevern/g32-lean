import HodgeLean.Foundations.IntegralHomology.StageTwo.FaceComplex
import HodgeLean.Foundations.Program.SchoenTransferC1a5BoundaryGeometryHelpers
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! Geometric realization of a finite union of standard simplex faces.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

def simplexFaceIso {n : ℕ} (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    (Δ[s.card - 1] : SSet.{0}) ≅ (SSet.stdSimplex.face s : SSet.{0}) :=
  SSet.stdSimplex.isoOfRepresentableBy (SSet.stdSimplex.faceRepresentableBy s _
    (monoEquivOfFin s (by
      rw [Fintype.card_coe]
      exact (Nat.sub_add_cancel (Finset.card_pos.mpr hs)).symm)))

theorem simplexFaceIso_hom_inclusion {n : ℕ}
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    (simplexFaceIso s hs).hom ≫ (SSet.stdSimplex.face s).ι =
      SSet.stdSimplex.map (SimplexCategory.Hom.mk
        ((OrderHom.Subtype.val (· ∈ s)).comp
          (monoEquivOfFin s (by
            rw [Fintype.card_coe]
            exact (Nat.sub_add_cancel (Finset.card_pos.mpr hs)).symm)).toOrderEmbedding.toOrderHom)) := rfl

end HodgeLean.Foundations.IntegralHomology.StageTwo

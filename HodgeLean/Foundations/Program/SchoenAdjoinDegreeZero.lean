import HodgeLean.Foundations.Program.SchoenCommonDegreeAdjoinGrading

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual homogeneous subalgebra retains exactly the original degree-zero coefficient ring. -/
def s2_adjoinDegreeZeroEquiv {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (s : Set A)
    [GradedRing (s2_subringGradedPiece 𝒜 (Algebra.adjoin (𝒜 0) s).toSubring)] :
    𝒜 0 ≃+* s2_subringGradedPiece 𝒜 (Algebra.adjoin (𝒜 0) s).toSubring 0 where
  toFun a := ⟨⟨a.val, (Algebra.adjoin (𝒜 0) s).algebraMap_mem a⟩, a.property⟩
  invFun a := ⟨a.val.val, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end HodgeLean.Foundations.Program

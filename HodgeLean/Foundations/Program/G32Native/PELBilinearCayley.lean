import HodgeLean.Foundations.Matrix.Cayley

noncomputable section
namespace HodgeLean.Foundations
open Matrix MatrixCayley
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The existing Cayley form identity also applies to bilinear forms over
fields with no chosen involution. -/
theorem pel_cayley_preserves_bilinear {E X : Matrix ι ι k}
    (hX : X.transpose * E + E * X = 0) (hdet : (1 + X).det ≠ 0) :
    (cayley X).transpose * E * cayley X = E := by
  letI : StarRing k := starRingOfComm
  letI : TrivialStar k := ⟨fun _ => rfl⟩
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (MatrixCayley.preservesForm (by simpa only
      [Matrix.conjTranspose_eq_transpose_of_trivial] using hX) hdet)

/-- The inverse Cayley chart of a bilinear isometry is skew for that form. -/
theorem pel_cayley_bilinear_skew {E g : Matrix ι ι k}
    (hg : g.transpose * E * g = E) (hdet : (1 + g).det ≠ 0) :
    (cayley g).transpose * E + E * cayley g = 0 := by
  letI : StarRing k := starRingOfComm
  letI : TrivialStar k := ⟨fun _ => rfl⟩
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (MatrixCayley.skewAdjoint (by simpa only
      [Matrix.conjTranspose_eq_transpose_of_trivial] using hg) hdet)

end HodgeLean.Foundations

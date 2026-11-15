import HodgeLean.Foundations.Program.PeriodComparisonModel

noncomputable section
open HodgeLean.Foundations HodgeLean.RealDefs HodgeLean.Adapters
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_musical_adjoint {L : Type} [AddCommGroup L]
    (Q : LinearMap.BilinForm ℤ L) (J K : L →+ L)
    (hQ : ∀ x y, Q (J x) y = Q x (K y)) (x : ℂ ⊗[ℤ] L) :
    b2bpol_musical L Q (b2_cplxMap J x) =
      (b60b_dualPrecomp K).baseChange ℂ (b2bpol_musical L Q x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c u =>
    rw [b2_cplxMap, LinearMap.baseChange_tmul,
      b2bpol_musical_tmul, b2bpol_musical_tmul, LinearMap.baseChange_tmul]
    congr 1
    ext v
    simp [b2b_flat, b60b_dualPrecomp, hQ]

end HodgeLean.Foundations.Program

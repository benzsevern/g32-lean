import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairKernelSeparation
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! An injective matrix realization of complex projective space.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped LinearAlgebra.Projectivization
namespace HodgeLean.WitnessSelection.StageTwo

/-- The normalized Hermitian kernel descends to complex projective lines.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
def s2e_pair_projectiveMatrix {ι : Type*} [Fintype ι] :
    Projectivization ℂ (ι → ℂ) → (ι → ι → ℂ) :=
  Projectivization.lift (fun v => s2e_pair_projectiveKernel v.val) (by
    intro a b c he
    have hc : c ≠ 0 := by
      intro hz
      apply a.property
      rw [he, hz, zero_smul]
    rw [he]
    exact s2e_pair_projectiveKernel_smul c hc b.val)

/-- Equal matrix realizations determine the same complex projective line.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_projectiveMatrix_injective {ι : Type*} [Fintype ι] :
    Function.Injective (s2e_pair_projectiveMatrix (ι := ι)) := by
  intro p q he
  induction p using Projectivization.ind with
  | _ v hv =>
    induction q using Projectivization.ind with
    | _ w hw =>
      change s2e_pair_projectiveKernel v = s2e_pair_projectiveKernel w at he
      obtain ⟨c, _, hcv⟩ := (s2e_pair_projectiveKernel_eq_iff_smul v hv w).mp he
      exact (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mpr ⟨c, hcv⟩

end HodgeLean.WitnessSelection.StageTwo

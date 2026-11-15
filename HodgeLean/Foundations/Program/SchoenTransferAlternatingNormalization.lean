import Mathlib.LinearAlgebra.ExteriorPower.Pairing

noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Tensor alternation followed by a multilinear map gives its alternating linearization. -/
theorem tensor_alternation_linearization {K M N : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (n : ℕ) (B : MultilinearMap K (fun _ : Fin n => M) N) :
    (PiTensorProduct.lift B).comp (exteriorPower.toTensorPower K M n) =
      exteriorPower.alternatingMapLinearEquiv B.alternatization := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.toTensorPower_apply_ιMulti, map_sum, Units.smul_def, map_zsmul,
    PiTensorProduct.lift.tprod, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]

/-- An alternating multilinear map receives the factorial normalization. -/
theorem tensor_alternation_factorial {K M N : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (n : ℕ) (B : AlternatingMap K M N (Fin n)) :
    (PiTensorProduct.lift B.toMultilinearMap).comp (exteriorPower.toTensorPower K M n) =
      (Nat.factorial n) • exteriorPower.alternatingMapLinearEquiv B := by
  rw [tensor_alternation_linearization, AlternatingMap.coe_alternatization,
    Fintype.card_fin, map_nsmul]

end HodgeLean.Foundations.Program

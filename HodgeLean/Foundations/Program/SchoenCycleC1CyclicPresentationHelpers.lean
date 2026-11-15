import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Adjoin.PowerBasis

/-! # Primitive Kummer presentations of finite cyclic function fields -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
namespace HodgeLean.Foundations.Program

/-- A finite cyclic extension containing the necessary roots of unity has
one power basis with its exact degree-sized Kummer minimal polynomial. -/
theorem s2e_c1_cyclic_kummer_powerBasis
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hroots : (primitiveRoots (Module.finrank K L) K).Nonempty) :
    ∃ (B : PowerBasis K L) (c : K),
      minpoly K B.gen = X ^ Module.finrank K L - C c ∧
      B.gen ^ Module.finrank K L = algebraMap K L c := by
  obtain ⟨z, ⟨c, hc⟩, hgen⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hroots
  have htop : Algebra.adjoin K ({z} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsAlgebraic.of_finite K z), hgen, IntermediateField.top_toSubalgebra]
  let B := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite K z) htop
  have hmonic := monic_X_pow_sub_C c (Nat.ne_of_gt (Module.finrank_pos : 0 < Module.finrank K L))
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top hc.symm hgen
  have hroot : aeval z (X ^ Module.finrank K L - C c : K[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C, ← hc, sub_self]
  exact ⟨B, c, (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm, hc.symm⟩

end HodgeLean.Foundations.Program

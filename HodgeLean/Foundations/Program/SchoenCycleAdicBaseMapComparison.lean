import HodgeLean.Foundations.Program.SchoenCycleAdicScalarChange
import HodgeLean.Foundations.Program.SchoenCycleAdicBasePowers
import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # The actual adic base map in relative module coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Adic scalar change identifies the relative linear base map with the actual adic algebra map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_scalar_change_base_map
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) (x : AdicCompletion I R) :
    s2e_adic_scalar_change_equiv I (AdicCompletion.map I (Algebra.linearMap R B) x) =
      s2e_adic_algebra_map I (I.map (algebraMap R B)) (Algebra.ofId R B)
        (s2e_base_map_preserves_extended_ideal_powers I) x := by
  let J := I.map (algebraMap R B)
  have hfiltration (n : ℕ) : (I ^ n • ⊤ : Submodule R B) =
      (J ^ n • ⊤ : Submodule B B).restrictScalars R := by
    simp [J, Ideal.smul_top_eq_map, Ideal.map_pow]
  let e (n : ℕ) : (B ⧸ (I ^ n • ⊤ : Submodule R B)) ≃ₗ[R]
      (B ⧸ (J ^ n • ⊤ : Submodule B B)) :=
    (Submodule.quotEquivOfEq _ _ (hfiltration n)).trans
      (Submodule.Quotient.restrictScalarsEquiv R (J ^ n • ⊤ : Submodule B B))
  apply AdicCompletion.ext
  intro n
  change e n ((Algebra.linearMap R B).reduceModIdeal (I ^ n) (x.val n)) =
    Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal B) (Algebra.ofId R B) _ (x.val n)
  refine Quotient.inductionOn' (x.val n) (fun r => ?_)
  change e n (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R B)) (algebraMap R B r)) =
    Submodule.Quotient.mk (p := (J ^ n • ⊤ : Submodule B B)) (algebraMap R B r)
  simp only [e, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.restrictScalarsEquiv_mk]

#print axioms s2e_adic_scalar_change_base_map
end HodgeLean.Foundations.Program

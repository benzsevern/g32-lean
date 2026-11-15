import HodgeLean.Foundations.Program.SchoenCycleAdicScalarChange
import HodgeLean.Foundations.Program.SchoenCycleAdicExtendedPowers
import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Action compatibility of adic scalar change -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Adic scalar change intertwines the relative module action with the actual algebra action on the extended-ideal adic ring.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_scalar_change_naturality
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) (f : B →ₐ[R] B) (x : AdicCompletion I B) :
    s2e_adic_scalar_change_equiv I (AdicCompletion.map I f.toLinearMap x) =
      s2e_adic_algebra_map (I.map (algebraMap R B)) (I.map (algebraMap R B)) f
        (s2e_linear_preserves_extended_ideal_powers I f.toLinearMap)
        (s2e_adic_scalar_change_equiv I x) := by
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
  change e n (f.toLinearMap.reduceModIdeal (I ^ n) (x.val n)) =
    Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal B) f _ (e n (x.val n))
  refine Quotient.inductionOn' (x.val n) (fun b => ?_)
  change e n (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R B)) (f b)) =
    Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal B) f _
      (e n (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R B)) b))
  simp only [e, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.restrictScalarsEquiv_mk]
  rfl

#print axioms s2e_adic_scalar_change_naturality
end HodgeLean.Foundations.Program

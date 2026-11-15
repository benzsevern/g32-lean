import HodgeLean.Foundations.Program.SchoenCycleStageDefs
import Mathlib.Algebra.Group.Commute.Units

/-! # Finite-order component translations
Powers of the retained generator preserve component immersions.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A finite-order endomorphism is invertible, as is every translate. -/
theorem s2e_generator_power_isIso {W : Over (Spec ↧ℂ)} (d : W ⟶ W)
    {m : ℕ} (hm : m ≠ 0) (hd : End.of d ^ m = 1) (t : ℕ) :
    IsIso (End.of d ^ t).asHom := by
  exact (isUnit_iff_isIso _).mp ((IsUnit.of_pow_eq_one hd hm).pow t)

/-- Every component translate remains an immersion. -/
theorem s2e_translated_component_isClosedImmersion
    {Q W : Over (Spec ↧ℂ)} (ι : Q ⟶ W) (d : W ⟶ W)
    [IsClosedImmersion ι.left] {m : ℕ} (hm : m ≠ 0)
    (hd : End.of d ^ m = 1) (t : ℕ) :
    IsClosedImmersion (ι ≫ (End.of d ^ t).asHom).left := by
  letI := s2e_generator_power_isIso d hm hd t
  change IsClosedImmersion (ι.left ≫ (End.of d ^ t).asHom.left)
  infer_instance

/-- A nonzero diagonal intersection detects every normalized character sum. -/
theorem s2e_weightedSum_ne_zero_of_pairing
    {V : Type*} [AddCommGroup V] [Module ℂ V] {m : ℕ} (hm : 0 < m)
    (v : Fin m → V) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (c : ℂ) (hc : c ≠ 0)
    (hv : ∀ t : Fin m, B (v ⟨0, hm⟩) (v t) = if t = ⟨0, hm⟩ then c else 0)
    (χ : ZMod m → ℂ) (hχ : χ 0 = 1) :
    s2e_weightedSum m χ v ≠ 0 := by
  classical
  intro h
  have he : B (v ⟨0, hm⟩) (s2e_weightedSum m χ v) = c := by
    simp only [s2e_weightedSum, map_sum, map_smul, hv]
    rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
    · simp only [Fin.val_zero, Nat.cast_zero, neg_zero, hχ, ite_true, one_smul]
    · intro b _ hb
      rw [if_neg hb, smul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  rw [h, map_zero] at he
  exact hc he.symm

end HodgeLean.Foundations.Program

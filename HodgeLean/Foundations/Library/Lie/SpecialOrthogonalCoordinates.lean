import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Library.Lie
open LieAlgebra.Orthogonal
attribute [local instance 100] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An elementary skew matrix. -/
def pelSkew (a b : n) : Matrix n n K := Matrix.single a b 1 - Matrix.single b a 1

lemma pelSkew_mem (a b : n) : pelSkew (K := K) a b ∈ so n K := by
  rw [mem_so]
  simp [pelSkew, Matrix.transpose_sub, Matrix.transpose_single, neg_sub]

lemma pelSkew_bracket_entry (a b : n) (X : Matrix n n K) (p q : n) :
    ⁅pelSkew (K := K) a b, X⁆ p q =
      (if p = a then X b q else 0) - (if p = b then X a q else 0) -
      (if q = b then X p a else 0) + (if q = a then X p b else 0) := by
  simp [Ring.lie_def, pelSkew, Matrix.mul_apply, Matrix.single, ite_and,
    sub_mul, mul_sub, Finset.sum_sub_distrib, eq_comm]
  ring

/-- Twice bracketing acts diagonally on the off-diagonal skew coordinates. -/
lemma pelSkew_double_entry (a b : n) (hab : a ≠ b)
    (X : Matrix n n K) (hX : X ∈ so n K) (p q : n) :
    ⁅pelSkew (K := K) a b, ⁅pelSkew (K := K) a b, X⁆⁆ p q =
      if ((p = a ∨ p = b) ∧ ¬(q = a ∨ q = b)) ∨
         (¬(p = a ∨ p = b) ∧ (q = a ∨ q = b)) then -X p q else 0 := by
  have hs : ∀ i j, X j i = -X i j := fun i j => congrFun (congrFun (mem_so n K X |>.mp hX) i) j
  have hd : ∀ i, X i i = 0 := by
    intro i
    have := hs i i
    linear_combination (norm := ring_nf) (1 / 2 : K) * this
  have habX := hs a b
  clear hs hX
  simp only [pelSkew_bracket_entry]
  by_cases hpa : p = a <;> by_cases hpb : p = b <;>
    by_cases hqa : q = a <;> by_cases hqb : q = b <;>
    simp_all [Ne.symm hab] <;> ring

/-- Four coordinate filters extract one elementary skew summand. -/
lemma pelSkew_extract (f : Fin 5 → n) (hf : Function.Injective f)
    (X : Matrix n n K) (hX : X ∈ so n K) :
    let D := fun (a b : n) (Y : Matrix n n K) => ⁅pelSkew (K := K) a b, ⁅pelSkew (K := K) a b, Y⁆⁆
    D (f 0) (f 2) (D (f 1) (f 3) (D (f 0) (f 4) (D (f 1) (f 4) X))) =
      X (f 0) (f 1) • pelSkew (K := K) (f 0) (f 1) := by
  let D := fun (a b : n) (Y : Matrix n n K) => ⁅pelSkew (K := K) a b, ⁅pelSkew (K := K) a b, Y⁆⁆
  have hm (a b : n) (Y : Matrix n n K) (hY : Y ∈ so n K) : D a b Y ∈ so n K :=
    (so n K).lie_mem (pelSkew_mem a b) ((so n K).lie_mem (pelSkew_mem a b) hY)
  have he (a b : Fin 5) (hab : a ≠ b) (Y : Matrix n n K) (hY : Y ∈ so n K) (p q : n) :
      D (f a) (f b) Y p q =
        if ((p = f a ∨ p = f b) ∧ ¬(q = f a ∨ q = f b)) ∨
           (¬(p = f a ∨ p = f b) ∧ (q = f a ∨ q = f b)) then -Y p q else 0 :=
    pelSkew_double_entry (f a) (f b) (hf.ne hab) Y hY p q
  have hs : X (f 1) (f 0) = -X (f 0) (f 1) :=
    congrFun (congrFun ((mem_so n K X).mp hX) (f 0)) (f 1)
  have hfeq (i j : Fin 5) : f i = f j ↔ i = j := hf.eq_iff
  change D _ _ (D _ _ (D _ _ (D _ _ X))) = _
  ext p q
  rw [he 0 2 (by decide) _ (hm _ _ _ (hm _ _ _ (hm _ _ _ hX))),
      he 1 3 (by decide) _ (hm _ _ _ (hm _ _ _ hX)),
      he 0 4 (by decide) _ (hm _ _ _ hX), he 1 4 (by decide) X hX]
  simp only [Matrix.smul_apply, smul_eq_mul, pelSkew, Matrix.sub_apply, Matrix.single_apply]
  have cases (z : n) : z = f 0 ∨ z = f 1 ∨ z = f 2 ∨ z = f 3 ∨ z = f 4 ∨
      (z ≠ f 0 ∧ z ≠ f 1 ∧ z ≠ f 2 ∧ z ≠ f 3 ∧ z ≠ f 4) := by
    tauto
  rcases cases p with hp | hp | hp | hp | hp | ⟨hp0, hp1, hp2, hp3, hp4⟩ <;>
    rcases cases q with hq | hq | hq | hq | hq | ⟨hq0, hq1, hq2, hq3, hq4⟩ <;>
    clear cases he hm D hX hf <;> simp_all [hfeq, eq_comm]

end HodgeLean.Foundations.Library.Lie

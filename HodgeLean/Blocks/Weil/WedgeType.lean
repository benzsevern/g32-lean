import HodgeLean.Blocks.Weil.Basic
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-! # Hodge and wedge types for Weil actions -/

open scoped TensorProduct

noncomputable section

namespace HodgeBlocks

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

namespace WeilAction

variable {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)

/-- The two classical weight-one Hodge pieces are disjoint, even without an effectivity
assumption. -/
theorem inf_H10_H01_Vs :
    (A.Vs ⊓ M.H (1, 0)) ⊓ (A.Vs ⊓ M.H (0, 1)) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hdis : Disjoint (M.H (1, 0)) (M.H (0, 1)) :=
    M.isInternal.submodule_iSupIndep.pairwiseDisjoint (by norm_num)
  exact hdis.le_bot ⟨hx.1.2, hx.2.2⟩

/-- Under the necessary effectivity/exhaustion hypothesis, the Weil eigenspace decomposes
along the `(1,0)` and `(0,1)` Hodge pieces.  The hypothesis is explicit because weight alone
does not exclude pieces such as `(2,-1)`. -/
theorem Vs_eq_sup
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) :
    A.Vs = (A.Vs ⊓ M.H (1, 0)) ⊔ (A.Vs ⊓ M.H (0, 1)) := by
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ M.H (1, 0) ⊔ M.H (0, 1) := by rw [hH]; trivial
    rcases Submodule.mem_sup.mp hxH with ⟨x10, hx10, x01, hx01, rfl⟩
    have hJ10 : A.Jc x10 ∈ M.H (1, 0) := A.preserves (1, 0) ⟨x10, hx10, rfl⟩
    have hJ01 : A.Jc x01 ∈ M.H (0, 1) := A.preserves (0, 1) ⟨x01, hx01, rfl⟩
    have heig := Module.End.mem_eigenspace_iff.mp hx
    have hz : (A.Jc x10 - omegaC d • x10) +
        (A.Jc x01 - omegaC d • x01) = 0 := by
      rw [map_add, smul_add] at heig
      calc
        _ = (A.Jc x10 + A.Jc x01) -
            (omegaC d • x10 + omegaC d • x01) := by abel
        _ = 0 := sub_eq_zero.mpr heig
    have h10mem : A.Jc x10 - omegaC d • x10 ∈ M.H (1, 0) :=
      sub_mem hJ10 ((M.H (1, 0)).smul_mem (omegaC d) hx10)
    have h01mem : A.Jc x01 - omegaC d • x01 ∈ M.H (0, 1) :=
      sub_mem hJ01 ((M.H (0, 1)).smul_mem (omegaC d) hx01)
    have hdis : Disjoint (M.H (1, 0)) (M.H (0, 1)) :=
      M.isInternal.submodule_iSupIndep.pairwiseDisjoint (by norm_num)
    have hz10 : A.Jc x10 - omegaC d • x10 = 0 := by
      have hother : A.Jc x10 - omegaC d • x10 ∈ M.H (0, 1) := by
        rw [eq_neg_of_add_eq_zero_left hz]
        exact (M.H (0, 1)).neg_mem h01mem
      have hb := hdis.le_bot ⟨h10mem, hother⟩
      rw [Submodule.mem_bot] at hb
      exact hb
    have hz01 : A.Jc x01 - omegaC d • x01 = 0 := by
      rw [hz10, zero_add] at hz
      exact hz
    apply Submodule.add_mem
    · apply Submodule.mem_sup_left
      exact ⟨Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp hz10), hx10⟩
    · apply Submodule.mem_sup_right
      exact ⟨Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp hz01), hx01⟩
  · exact sup_le (inf_le_left) (inf_le_left)

end WeilAction

section WedgeType

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The span of decomposable `(a,b)` wedges: the first `a` factors lie in `P` and the
last `b` factors lie in `Q`.  This intrinsic span has no choices of bases or representatives. -/
def wedgeType (P Q : Submodule ℂ E) (a b : ℕ) :
    Submodule ℂ (⋀[ℂ]^(a + b) E) :=
  Submodule.span ℂ {x | ∃ p : Fin a → E, (∀ i, p i ∈ P) ∧
    ∃ q : Fin b → E, (∀ i, q i ∈ Q) ∧
      x = exteriorPower.ιMulti ℂ (a + b)
        (Fin.append p q)}

/-- A decomposable wedge with its first factors in `P` and last factors in `Q` belongs to
`wedgeType`; this is the generating containment built into the definition. -/
theorem ιMulti_append_mem_wedgeType (P Q : Submodule ℂ E) (a b : ℕ)
    (p : Fin a → E) (hp : ∀ i, p i ∈ P)
    (q : Fin b → E) (hq : ∀ i, q i ∈ Q) :
    exteriorPower.ιMulti ℂ (a + b) (Fin.append p q) ∈
      wedgeType P Q a b := by
  apply Submodule.subset_span
  exact ⟨p, hp, q, hq, rfl⟩

/-- Wedge-product formulation of `ιMulti_append_mem_wedgeType`. -/
theorem wedge_ιMulti_mem_wedgeType (P Q : Submodule ℂ E) (a b : ℕ)
    (p : Fin a → E) (hp : ∀ i, p i ∈ P)
    (q : Fin b → E) (hq : ∀ i, q i ∈ Q) :
    exteriorPower.wedge ℂ E a b
        (exteriorPower.ιMulti ℂ a p) (exteriorPower.ιMulti ℂ b q) ∈
      wedgeType P Q a b := by
  rw [show exteriorPower.wedge ℂ E a b
      (exteriorPower.ιMulti ℂ a p) (exteriorPower.ιMulti ℂ b q) =
      exteriorPower.ιMulti ℂ (a + b) (Fin.append p q) by
    apply Subtype.ext
    exact ExteriorAlgebra.ιMulti_mul_ιMulti p q]
  exact ιMulti_append_mem_wedgeType P Q a b p hp q hq

end WedgeType
end HodgeBlocks

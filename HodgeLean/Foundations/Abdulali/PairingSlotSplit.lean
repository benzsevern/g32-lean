import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Fin

namespace HodgeLean.Foundations.Abdulali

/-- The partner of a slot in a pairing encoded by two-slot blocks. -/
def pairingPartner {P S : Type*} (e : (P × Fin 2) ≃ S) : Equiv.Perm S :=
  e.symm.trans ((Equiv.prodCongr (Equiv.refl P) (Equiv.swap 0 1)).trans e)

/-- Taking the partner twice returns the initial slot. -/
theorem pairingPartner_involutive {P S : Type*} (e : (P × Fin 2) ≃ S) :
    Function.Involutive (pairingPartner e) := by
  intro s
  obtain ⟨⟨p, j⟩, rfl⟩ := e.surjective s
  simp only [pairingPartner, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.symm_apply_apply, Prod.map_apply, Equiv.refl_apply, Equiv.swap_apply_self]

/-- Every slot has a different partner. -/
theorem pairingPartner_ne_self {P S : Type*} (e : (P × Fin 2) ≃ S) (s : S) :
    pairingPartner e s ≠ s := by
  obtain ⟨⟨p, j⟩, rfl⟩ := e.surjective s
  intro h
  have hh := e.injective h
  simp only [pairingPartner, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply, Equiv.refl_apply, Prod.mk.injEq] at hh
  fin_cases j <;> norm_num at hh

/-- A pairing either joins two extra slots or embeds all extra slots among original partners. -/
theorem pairingPartner_split {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J)) :
    (∃ j j' : J, j ≠ j' ∧ pairingPartner e (Sum.inr j) = Sum.inr j') ∨
    ∃ f : J ↪ I, ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j) := by
  classical
  by_cases h : ∃ j j' : J, pairingPartner e (Sum.inr j) = Sum.inr j'
  · left
    obtain ⟨j, j', hj⟩ := h
    refine ⟨j, j', ?_, hj⟩
    rintro rfl
    exact pairingPartner_ne_self e _ hj
  · right
    have hi (j : J) : ∃ i : I, pairingPartner e (Sum.inr j) = Sum.inl i := by
      cases hj : pairingPartner e (Sum.inr j) with
      | inl i => exact ⟨i, rfl⟩
      | inr j' => exact False.elim (h ⟨j, j', hj⟩)
    choose f hf using hi
    refine ⟨⟨f, ?_⟩, hf⟩
    intro j k hjk
    apply Sum.inr_injective
    apply (pairingPartner e).injective
    rw [hf, hf, hjk]

end HodgeLean.Foundations.Abdulali

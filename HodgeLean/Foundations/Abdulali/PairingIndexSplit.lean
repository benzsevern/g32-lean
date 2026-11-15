import HodgeLean.Foundations.Abdulali.PairingSlotSplit
import Mathlib.Logic.Equiv.Set

namespace HodgeLean.Foundations.Abdulali

/-- Two slots in one pairing block coincide or are partners. -/
theorem pairingIndex_eq_or_partner {P S : Type*} (e : (P × Fin 2) ≃ S)
    (x y : S) (h : (e.symm x).1 = (e.symm y).1) :
    x = y ∨ pairingPartner e x = y := by
  obtain ⟨⟨p, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨q, j⟩, rfl⟩ := e.surjective y
  simp only [Equiv.symm_apply_apply] at h
  subst q
  fin_cases i <;> fin_cases j
  · exact Or.inl rfl
  · right; simp only [pairingPartner, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
    congr 2
  · right; simp only [pairingPartner, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
    congr 2
  · exact Or.inl rfl

/-- Passing to the partner leaves the pairing-block index unchanged. -/
theorem pairingIndex_partner {P S : Type*} (e : (P × Fin 2) ≃ S) (x : S) :
    (e.symm (pairingPartner e x)).1 = (e.symm x).1 := by
  simp only [pairingPartner, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply, Prod.map_fst, Equiv.refl_apply]

/-- An original slot shares an extra slot's pairing index exactly at its assigned partner. -/
theorem pairingIndex_crossing_iff {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J))
    (f : J ↪ I) (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j))
    (i : I) (j : J) :
    (e.symm (Sum.inl i)).1 = (e.symm (Sum.inr j)).1 ↔ i = f j := by
  constructor
  · intro h
    rcases pairingIndex_eq_or_partner e (Sum.inl i) (Sum.inr j) h with h | h
    · cases h
    · have hh := congrArg (pairingPartner e) h
      rw [pairingPartner_involutive, hf] at hh
      exact Sum.inl_injective hh
  · rintro rfl
    rw [← hf, pairingIndex_partner]

/-- With all extra slots paired to originals, their pairing-block indices are distinct. -/
theorem pairingIndex_extra_injective {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J))
    (f : J ↪ I) (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j)) :
    Function.Injective (fun j : J => (e.symm (Sum.inr j)).1) := by
  intro j k h
  apply f.injective
  apply (pairingIndex_crossing_iff e f hf (f j) k).mp
  exact ((pairingIndex_crossing_iff e f hf (f j) j).mpr rfl).trans h

/-- A pairing block unused by extra slots has both its slots among the originals. -/
theorem pairingIndex_remaining_slot {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J))
    (p : P) (hp : p ∉ Set.range (fun j : J => (e.symm (Sum.inr j)).1))
    (b : Fin 2) : ∃ i : I, e (p, b) = Sum.inl i := by
  cases h : e (p, b) with
  | inl i => exact ⟨i, rfl⟩
  | inr j =>
    apply False.elim
    apply hp
    refine ⟨j, ?_⟩
    change (e.symm (Sum.inr j)).1 = p
    rw [← h, Equiv.symm_apply_apply]

end HodgeLean.Foundations.Abdulali

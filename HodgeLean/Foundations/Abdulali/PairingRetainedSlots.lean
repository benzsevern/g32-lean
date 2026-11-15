import HodgeLean.Foundations.Abdulali.PairingIndexSplit

noncomputable section
namespace HodgeLean.Foundations.Abdulali

/-- The original slots, indexed by remaining two-slot blocks and crossing partners. -/
def pairingRetainedSlot {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J))
    (f : J ↪ I) :
    ({p : P // p ∉ Set.range (fun j : J => (e.symm (Sum.inr j)).1)} × Fin 2) ⊕ J → I :=
  Sum.elim (fun p => Classical.choose (pairingIndex_remaining_slot e p.1.val p.1.property p.2)) f

/-- A remaining block slot maps back to its exact original slot. -/
theorem pairingRetainedSlot_remaining {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J))
    (f : J ↪ I)
    (p : {p : P // p ∉ Set.range (fun j : J => (e.symm (Sum.inr j)).1)}) (b : Fin 2) :
    e (p.val, b) = Sum.inl (pairingRetainedSlot e f (Sum.inl (p, b))) :=
  Classical.choose_spec (pairingIndex_remaining_slot e p.val p.property b)

/-- Remaining block slots and crossing partners give distinct original slots. -/
theorem pairingRetainedSlot_injective {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J))
    (f : J ↪ I) (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j)) :
    Function.Injective (pairingRetainedSlot e f) := by
  have hi (p : {p : P // p ∉ Set.range (fun j : J => (e.symm (Sum.inr j)).1)})
      (b : Fin 2) :
      e.symm (Sum.inl (pairingRetainedSlot e f (Sum.inl (p, b)))) = (p.val, b) := by
    rw [← pairingRetainedSlot_remaining, Equiv.symm_apply_apply]
  have hc (p : {p : P // p ∉ Set.range (fun j : J => (e.symm (Sum.inr j)).1)})
      (b : Fin 2) (j : J) : pairingRetainedSlot e f (Sum.inl (p, b)) ≠ f j := by
    intro h
    have hh := (pairingIndex_crossing_iff e f hf _ j).mpr h
    rw [hi] at hh
    exact p.property ⟨j, hh.symm⟩
  intro x y h
  cases x with
  | inl p =>
    cases y with
    | inl q =>
      have hh := congrArg (fun i : I => e.symm (Sum.inl i)) h
      rw [hi, hi] at hh
      apply congrArg Sum.inl
      apply Prod.ext
      · exact Subtype.ext (congrArg (fun x : P × Fin 2 => x.1) hh)
      · exact congrArg (fun x : P × Fin 2 => x.2) hh
    | inr j => exact False.elim (hc p.1 p.2 j h)
  | inr j =>
    cases y with
    | inl q => exact False.elim (hc q.1 q.2 j h.symm)
    | inr k => exact congrArg Sum.inr (f.injective h)

/-- Every original slot is either in a remaining pair or is a crossing partner. -/
theorem pairingRetainedSlot_surjective {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J))
    (f : J ↪ I) (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j)) :
    Function.Surjective (pairingRetainedSlot e f) := by
  classical
  intro i
  let p := (e.symm (Sum.inl i)).1
  let b := (e.symm (Sum.inl i)).2
  by_cases hp : p ∈ Set.range (fun j : J => (e.symm (Sum.inr j)).1)
  · obtain ⟨j, hj⟩ := hp
    have hi : i = f j := (pairingIndex_crossing_iff e f hf i j).mp hj.symm
    exact ⟨Sum.inr j, hi.symm⟩
  · let k : {p : P // p ∉ Set.range (fun j : J => (e.symm (Sum.inr j)).1)} := ⟨p, hp⟩
    refine ⟨Sum.inl (k, b), ?_⟩
    apply Sum.inl_injective
    rw [← pairingRetainedSlot_remaining]
    exact e.apply_symm_apply (Sum.inl i)

/-- Reindex the originals as remaining pair slots followed by crossing partners. -/
def pairingRetainedEquiv {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J))
    (f : J ↪ I) (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j)) :
    (({p : P // p ∉ Set.range (fun j : J => (e.symm (Sum.inr j)).1)} × Fin 2) ⊕ J) ≃ I :=
  Equiv.ofBijective (pairingRetainedSlot e f)
    ⟨pairingRetainedSlot_injective e f hf, pairingRetainedSlot_surjective e f hf⟩

/-- Reindex pairing blocks as remaining blocks followed by the blocks meeting extras. -/
def pairingBlockEquiv {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J))
    (f : J ↪ I) (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j)) :
    ({p : P // p ∉ Set.range (fun j : J => (e.symm (Sum.inr j)).1)} ⊕ J) ≃ P := by
  classical
  let q : J → P := fun j => (e.symm (Sum.inr j)).1
  exact (Equiv.sumCongr (Equiv.refl _) (Equiv.ofInjective q (pairingIndex_extra_injective e f hf))).trans
    ((Equiv.sumComm _ _).trans (Equiv.Set.sumCompl (Set.range q)))

/-- The block equivalence keeps remaining indices and sends an extra to its original block. -/
theorem pairingBlockEquiv_apply {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J))
    (f : J ↪ I) (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j))
    (x : {p : P // p ∉ Set.range (fun j : J => (e.symm (Sum.inr j)).1)} ⊕ J) :
    pairingBlockEquiv e f hf x =
      Sum.elim Subtype.val (fun j : J => (e.symm (Sum.inr j)).1) x := by
  classical
  cases x <;> rfl

/-- Original-slot reindexing agrees with pairing-block reindexing. -/
theorem pairingRetainedEquiv_index {P I J : Type*} (e : (P × Fin 2) ≃ (I ⊕ J))
    (f : J ↪ I) (hf : ∀ j, pairingPartner e (Sum.inr j) = Sum.inl (f j))
    (x : ({p : P // p ∉ Set.range (fun j : J => (e.symm (Sum.inr j)).1)} × Fin 2) ⊕ J) :
    (e.symm (Sum.inl (pairingRetainedEquiv e f hf x))).1 =
      pairingBlockEquiv e f hf (Sum.elim (fun p => Sum.inl p.1) Sum.inr x) := by
  rw [pairingBlockEquiv_apply]
  cases x with
  | inl p =>
    change (e.symm (Sum.inl (pairingRetainedSlot e f (Sum.inl p)))).1 = p.1.val
    rw [← pairingRetainedSlot_remaining, Equiv.symm_apply_apply]
  | inr j => exact (pairingIndex_crossing_iff e f hf (f j) j).mpr rfl

end HodgeLean.Foundations.Abdulali

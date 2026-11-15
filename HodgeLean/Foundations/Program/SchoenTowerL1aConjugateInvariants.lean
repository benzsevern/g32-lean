import Mathlib.Algebra.Ring.Equiv

/-! # Transport of actual invariant-ring identifications

Invariant images transport through actual section-ring isomorphisms.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Conjugating the base and source section rings preserves injectivity and the invariant-image identification.
Source: Stacks Project, tag 04A9, invariant functions under identification of rings. -/
theorem s2v_l1a_conjugate_invariant_image
    {R S R' S' T : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (p : R →+* S) (ρ : T → (S →+* S))
    (hp : Function.Injective p) (himage : ∀ s, s ∈ Set.range p ↔ ∀ t, ρ t s = s)
    (eR : R' ≃+* R) (eS : S' ≃+* S)
    (q : R' →+* S') (σ : T → (S' →+* S'))
    (hq : ∀ r, eS (q r) = p (eR r))
    (hσ : ∀ t s, eS (σ t s) = ρ t (eS s)) :
    Function.Injective q ∧ ∀ s, s ∈ Set.range q ↔ ∀ t, σ t s = s := by
  constructor
  · intro x y h
    apply eR.injective
    apply hp
    rw [← hq, ← hq, h]
  · intro s
    have hrange : s ∈ Set.range q ↔ eS s ∈ Set.range p := by
      constructor
      · rintro ⟨r, rfl⟩
        exact ⟨eR r, (hq r).symm⟩
      · rintro ⟨r, hr⟩
        refine ⟨eR.symm r, eS.injective ?_⟩
        rw [hq, eR.apply_symm_apply, hr]
    rw [hrange, himage]
    exact forall_congr' (fun t => by rw [← hσ, eS.injective.eq_iff])

end HodgeLean.Foundations.Program

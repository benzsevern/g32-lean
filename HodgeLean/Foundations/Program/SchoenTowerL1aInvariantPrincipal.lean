import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.RingTheory.Ideal.Basic

/-! # Principal refinements descending through finite invariants

Implication from nonvanishing on a finite orbit to an invariant principal
refinement descending through the actual invariant section image.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Multiplying the translates of a section gives a descended invariant
section, retaining nonvanishing on its orbit and divisibility by that section.
Source: Stacks Project, tag 04A9, invariant functions for finite group quotients. -/
theorem s2v_l1a_invariant_principal_refinement
    {A B K G : Type*} [CommRing A] [CommRing B] [CommRing K] [IsDomain K]
    [Group G] [Fintype G] [MulSemiringAction G A]
    (q : B →+* A)
    (himage : ∀ a : A, a ∈ Set.range q ↔ ∀ g : G, g • a = a)
    (φ : A →+* K) (I : Ideal A) (d : A) (hd : d ∈ I)
    (hne : ∀ g : G, φ (g • d) ≠ 0) :
    ∃ c : B, q c ∈ I ∧ φ (q c) ≠ 0 ∧ d ∣ q c := by
  classical
  let N : A := ∏ g : G, g • d
  obtain ⟨c, hc⟩ := (himage N).mpr (fun g => Finset.smul_prod_perm d g)
  have hdvd : d ∣ N := by
    simpa only [one_smul] using
      (Finset.dvd_prod_of_mem (fun g : G => g • d) (Finset.mem_univ (1 : G)))
  refine ⟨c, ?_, ?_, hc ▸ hdvd⟩
  · rw [hc]
    obtain ⟨r, hr⟩ := hdvd
    rw [hr]
    exact I.mul_mem_right r hd
  · rw [hc]
    change φ (∏ g : G, g • d) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun g _ => hne g)

end HodgeLean.Foundations.Program

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-! # First-order interpolation for curve parameters

Implication from distinct maximal ideals and chosen nonzero first-order classes
to one element realizing all prescribed classes. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Prescribed values and nonzero first-order classes at distinct maximal ideals can be interpolated.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10, Chinese remainder theorem. -/
theorem s2v_l1a_nonzero_first_jet_interpolation
    {R κ : Type*} [CommRing R] [Finite κ]
    (m : κ → Ideal R) [∀ k, (m k).IsMaximal] (hm : Function.Injective m)
    (c u : κ → R) (hu : ∀ k, u k ∈ m k) (hnu : ∀ k, u k ∉ m k ^ 2) :
    ∃ f : R, ∀ k, f - c k ∈ m k ∧ f - c k ∉ m k ^ 2 := by
  have hcop : Pairwise (fun i j => IsCoprime (m i ^ 2) (m j ^ 2)) := by
    intro i j hij
    exact (Ideal.isCoprime_of_isMaximal (hm.ne hij)).pow
  obtain ⟨f, hf⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun k => c k + u k)
  refine ⟨f, ?_⟩
  intro k
  have hid : f - c k = (f - (c k + u k)) + u k := by ring
  constructor
  · rw [hid]
    exact (m k).add_mem (Ideal.pow_le_self (by omega) (hf k)) (hu k)
  · intro hbad
    apply hnu k
    have hid' : u k = (f - c k) - (f - (c k + u k)) := by ring
    rw [hid']
    exact (m k ^ 2).sub_mem hbad (hf k)

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenTowerReynolds

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Compatible values on a finite family of commuting retracts extend to the ambient algebra.
Source: SGA 1, Exposé V, §1, affine invariant quotients; explicit finite retraction argument. -/
theorem s2t_extend_compatible_retractions {K A I : Type*}
    [CommRing K] [CommRing A] [Algebra K A]
    (r : I → A →ₐ[K] A) (h : I → A)
    (hid : ∀ i a, r i (r i a) = r i a)
    (hcomm : ∀ i j a, r i (r j a) = r j (r i a))
    (hfix : ∀ i, r i (h i) = h i)
    (hcompat : ∀ i j, r i (h j) = r j (h i)) (s : Finset I) :
    ∃ a : A, ∀ i ∈ s, r i a = h i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp only [Finset.notMem_empty, false_implies, implies_true]⟩
  | @insert i s hi ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨a + h i - r i a, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [map_sub, map_add, hfix, hid]
      exact add_sub_cancel_left _ _
    · rw [map_sub, map_add, hcomm, ha j hj, hcompat]
      exact add_sub_cancel_right _ _

/-- Equivariant compatible values have an invariant extension in characteristic zero.
Source: SGA 1, Exposé V, §1, affine invariant quotients; finite retractions and averaging. -/
theorem s2t_extend_invariant_retractions {K A I G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    [Fintype I] [MulAction G I]
    (r : I → A →ₐ[K] A) (h : I → A)
    (hid : ∀ i a, r i (r i a) = r i a)
    (hcomm : ∀ i j a, r i (r j a) = r j (r i a))
    (hfix : ∀ i, r i (h i) = h i)
    (hcompat : ∀ i j, r i (h j) = r j (h i))
    (hr : ∀ (g : G) i a, r (g • i) (g • a) = g • r i a)
    (hh : ∀ (g : G) i, g • h i = h (g • i)) :
    ∃ a : FixedPoints.subalgebra K A G, ∀ i, r i (a : A) = h i := by
  obtain ⟨a, ha⟩ := s2t_extend_compatible_retractions r h hid hcomm hfix hcompat Finset.univ
  have ha' (i : I) : r i a = h i := ha i (Finset.mem_univ i)
  have havg (i : I) (g : G) : r i (g • a) = h i := by
    have he := hr g (g⁻¹ • i) a
    rw [smul_inv_smul, ha', hh, smul_inv_smul] at he
    exact he
  refine ⟨s2t_reynolds K A G a, ?_⟩
  intro i
  change r i ((Fintype.card G : K)⁻¹ • ∑ g : G, g • a) = h i
  rw [map_smul, map_sum]
  simp only [havg, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCycleInvariantJets

/-! # Ideal contraction for finite invariant rings -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Extension followed by contraction preserves every ideal of a finite invariant ring
in characteristic zero.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1,
§1, the averaging projection onto invariants. -/
theorem s2e_invariant_ring_ideal_contraction
    (R A G : Type*) [CommRing R] [CommRing A] [Algebra ℂ A]
    [Group G] [Fintype G] (a : G →* (A ≃ₐ[ℂ] A)) (f : R →+* A)
    (hf : Function.Injective f) (hfix : ∀ g r, a g (f r) = f r)
    (hdesc : ∀ b : A, (∀ g, a g b = b) → ∃ r, f r = b)
    (J : Ideal R) : (J.map f).comap f = J := by
  classical
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let v : A := algebraMap ℂ A ((Fintype.card G : ℂ)⁻¹)
  let av (b : A) : A := v * ∑ g : G, a g b
  have hv : v * (Fintype.card G : A) = 1 := by
    dsimp only [v]
    rw [← map_natCast (algebraMap ℂ A), ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hav (b : A) (g : G) : a g (av b) = av b := by
    dsimp only [av, v]
    rw [map_mul, (a g).commutes, map_sum]
    congr 1
    simp only [← AlgEquiv.mul_apply, ← map_mul]
    rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h => a h b)]
  have hav_range (b : A) : ∃ r, f r = av b := hdesc (av b) (hav b)
  have hav_fix (r : R) : av (f r) = f r := by
    simp only [av, hfix, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, hv, one_mul]
  have hav_add (b c : A) : av (b + c) = av b + av c := by
    simp only [av, map_add, Finset.sum_add_distrib, mul_add]
  have hav_mul (b : A) (r : R) : av (b * f r) = av b * f r := by
    simp only [av, map_mul, hfix, ← Finset.sum_mul, mul_assoc]
  have hmem (x : A) (hx : x ∈ J.map f) : ∃ r ∈ J, f r = av x := by
    suffices ∀ b : A, ∃ r ∈ J, f r = av (b * x) by
      simpa only [one_mul] using this 1
    change x ∈ Submodule.span A (f '' (J : Set R)) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨r, hr, rfl⟩
      intro b
      obtain ⟨s, hs⟩ := hav_range b
      refine ⟨s * r, J.mul_mem_left s hr, ?_⟩
      rw [map_mul, hs, hav_mul]
    | zero =>
      intro b
      refine ⟨0, J.zero_mem, ?_⟩
      simp only [av, mul_zero, map_zero, Finset.sum_const_zero]
    | add x y hx hy ihx ihy =>
      intro b
      obtain ⟨r, hr, hr'⟩ := ihx b
      obtain ⟨s, hs, hs'⟩ := ihy b
      refine ⟨r + s, J.add_mem hr hs, ?_⟩
      rw [map_add, hr', hs', mul_add, hav_add]
    | smul c x hx ih =>
      intro b
      simpa only [smul_eq_mul, mul_assoc] using ih (b * c)
  apply le_antisymm
  · intro r hr
    obtain ⟨s, hs, he⟩ := hmem (f r) hr
    rw [hav_fix] at he
    exact hf he ▸ hs
  · exact Ideal.le_comap_map

#print axioms s2e_invariant_ring_ideal_contraction
end HodgeLean.Foundations.Program

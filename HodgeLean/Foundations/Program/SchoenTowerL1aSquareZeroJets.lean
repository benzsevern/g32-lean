import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-! # Detecting nonzero first-order classes by square-zero lifts

A nonzero infinitesimal component witnesses failure of membership in the
square of a point ideal. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A square-zero lift detects a nonzero class modulo the square of the point kernel.
Source: Hartshorne, Algebraic Geometry, II.8, tangent vectors and dual numbers. -/
theorem s2v_l1a_square_zero_detects_first_jet
    {A K : Type*} [CommRing A] [CommRing K]
    (ev : A →+* K) (l : A →+* TrivSqZeroExt K K)
    (hl : (TrivSqZeroExt.fstHom K K K).toRingHom.comp l = ev)
    (r : A) (hr : ev r = 0) (hn : (l r).snd ≠ 0) :
    r ∈ RingHom.ker ev ∧ r ∉ RingHom.ker ev ^ 2 := by
  refine ⟨hr, ?_⟩
  have hmap : Ideal.map l (RingHom.ker ev) ≤ TrivSqZeroExt.kerIdeal K K := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change (l x).fst = 0
    exact (DFunLike.congr_fun hl x).trans hx
  intro hbad
  have hm := Ideal.mem_map_of_mem l hbad
  rw [Ideal.map_pow] at hm
  have hsq : Ideal.map l (RingHom.ker ev) ^ 2 ≤ ⊥ := by
    calc
      _ ≤ TrivSqZeroExt.kerIdeal K K ^ 2 := pow_le_pow_left' hmap 2
      _ = ⊥ := TrivSqZeroExt.kerIdeal_sq K K
  have heq : l r = 0 := hsq hm
  exact hn (by rw [heq]; rfl)

end HodgeLean.Foundations.Program

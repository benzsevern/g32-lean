import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComponentLabels

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual selector and parameter eigenvalues determine the successor component and the common parameter dilation, including the final label. -/
theorem binomial_labelled_deck_coordinates
    {X : Type*} (g : ℕ) (hg : 0 < g) (κ ζ c : ℂ) (hκ : κ ≠ 0)
    (hζ : IsPrimitiveRoot ζ g)
    (E : X ≃ ZMod g × ℂ) (q t : X → ℂ) (D : X → X)
    (hq : ∀ x, q x = κ * ζ ^ (E x).1.val)
    (ht : ∀ x, t x = (E x).2)
    (hqD : ∀ x, q (D x) = ζ * q x)
    (htD : ∀ x, t (D x) = c * t x) :
    ∀ x, E (D x) = ((E x).1 + 1, c * (E x).2) := by
  letI : NeZero g := ⟨Nat.ne_of_gt hg⟩
  have hsucc (l : ZMod g) : ζ ^ (l + 1).val = ζ * ζ ^ l.val := by
    have hm : (l + 1).val ≡ l.val + 1 [MOD g] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ g).mp
      simp only [ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_one]
    rw [pow_eq_pow_of_modEq hm hζ.pow_eq_one, pow_add, pow_one, mul_comm]
  intro x
  apply Prod.ext
  · obtain ⟨l, _, hl⟩ := binomial_root_label g hg κ ζ (q (D x)) hκ hζ
      (by rw [hq]; simp only [mul_pow, ← pow_mul];
          rw [Nat.mul_comm (E (D x)).1.val g, pow_mul, hζ.pow_eq_one, one_pow, mul_one])
    have hfirst : q (D x) = κ * ζ ^ ((E x).1 + 1).val := by
      rw [hqD, hq, hsucc]
      ring
    exact (hl (E (D x)).1 (hq (D x))).trans (hl ((E x).1 + 1) hfirst).symm
  · exact (ht (D x)).symm.trans ((htD x).trans (congrArg (fun z => c * z) (ht x)))

end AlgebraicGeometry.RamifiedNormalization.StageFour

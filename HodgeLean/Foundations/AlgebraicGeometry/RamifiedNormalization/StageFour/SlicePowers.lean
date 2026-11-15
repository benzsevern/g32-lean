import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Powers of the restricted morphism retain the first pullback projection. -/
theorem sliceDeck_pow_fst {W B' B : Over (Spec ↧ℂ)} (β : W ⟶ B')
    (b : B' ⟶ B) (x : ComplexPoint B) (d : W ⟶ W) (hd : d ≫ β = β)
    (n : ℕ) :
    ((End.of (sliceDeck β b x d hd)) ^ n).asHom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ ((End.of d) ^ n).asHom := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, End.mul_asHom]
    rw [Category.assoc]
    rw [ih, ← Category.assoc]
    simp only [sliceDeck, pullback.lift_fst, Category.assoc]

/-- Powers of the restricted morphism retain the second pullback projection. -/
theorem sliceDeck_pow_snd {W B' B : Over (Spec ↧ℂ)} (β : W ⟶ B')
    (b : B' ⟶ B) (x : ComplexPoint B) (d : W ⟶ W) (hd : d ≫ β = β)
    (n : ℕ) :
    ((End.of (sliceDeck β b x d hd)) ^ n).asHom ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, End.mul_asHom]
    rw [Category.assoc]
    rw [ih]
    simp only [sliceDeck, pullback.lift_snd]

/-- Every exponent giving identity before restriction also gives identity on the slice. -/
theorem sliceDeck_pow_eq_one {W B' B : Over (Spec ↧ℂ)} (β : W ⟶ B')
    (b : B' ⟶ B) (x : ComplexPoint B) (d : W ⟶ W) (hd : d ≫ β = β)
    (n : ℕ) (hn : (End.of d) ^ n = 1) :
    (End.of (sliceDeck β b x d hd)) ^ n = 1 := by
  apply End.ext
  apply pullback.hom_ext
  · rw [sliceDeck_pow_fst, hn]
    simp
  · rw [sliceDeck_pow_snd]
    simp

/-- Evaluate an endomorphism power by iterating its map on complex points. -/
theorem point_map_end_pow {F : Over (Spec ↧ℂ)} (D : F ⟶ F)
    (n : ℕ) (z : ComplexPoint F) :
    Point.map ((End.of D) ^ n).asHom z = (Point.map D)^[n] z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ, End.mul_asHom, Point.map_comp_apply]
    rw [ih, Function.iterate_succ_apply]

/-- A point with no smaller positive return detects the exact scheme-morphism order. -/
theorem sliceDeck_order_of_point {W B' B : Over (Spec ↧ℂ)} (β : W ⟶ B')
    (b : B' ⟶ B) (x : ComplexPoint B) (d : W ⟶ W) (hd : d ≫ β = β)
    (n : ℕ) (hn : 0 < n) (hpow : (End.of d) ^ n = 1)
    (z : ComplexPoint (coveringSlice β b x))
    (hz : ∀ k, k < n → 0 < k →
      (Point.map (sliceDeck β b x d hd))^[k] z ≠ z) :
    orderOf (End.of (sliceDeck β b x d hd)) = n := by
  apply (orderOf_eq_iff hn).mpr
  refine ⟨sliceDeck_pow_eq_one β b x d hd n hpow, ?_⟩
  intro k hkn hk hkeq
  apply hz k hkn hk
  rw [← point_map_end_pow, hkeq]
  rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour

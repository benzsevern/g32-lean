import HodgeLean.Foundations.Program.SchoenCoordinateActionLaws

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Powers of the retained residual generator lift to the corresponding first-coordinate translations. -/
theorem s2v_l1b_residual_generator_powers
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) (hn : 0 < n) (q : g3_power Y n ⟶ W) (d : W ⟶ W)
    (hgen : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q)
    (k : ℕ) :
    q ≫ (End.of d ^ k).asHom =
      s2_action S Y a e n (s2_delta S n hn (k : ZMod S.m)) 1 ≫ q := by
  induction k with
  | zero =>
    have hz : s2_delta S n hn (0 : ZMod S.m) = 0 := by
      funext j
      simp only [s2_delta, ite_self, Pi.zero_apply]
    rw [Nat.cast_zero, hz, (s2_coordinateAction_laws S Y a e ha1 hamul n).1]
    simp only [pow_zero, End.one_def, Category.comp_id, Category.id_comp]
  | succ k ih =>
    rw [pow_succ, End.mul_asHom]
    change q ≫ (d ≫ (End.of d ^ k).asHom) = _
    rw [← Category.assoc, hgen, Category.assoc, ih, ← Category.assoc,
      (s2_coordinateAction_laws S Y a e ha1 hamul n).2]
    have he : (fun j => s2_delta S n hn (k : ZMod S.m) j +
        s2_delta S n hn 1 ((1 : Equiv.Perm (Fin n)).symm j)) =
        s2_delta S n hn ((k + 1 : ℕ) : ZMod S.m) := by
      funext j
      simp only [Equiv.Perm.one_symm, Equiv.Perm.one_apply]
      by_cases hj : j = ⟨0, hn⟩
      · simp only [s2_delta, hj, ite_true, Nat.cast_add, Nat.cast_one]
      · simp only [s2_delta, hj, ite_false, add_zero]
    rw [he, one_mul]

/-- Coordinate actions with a given translation sum induce that power of the retained residual generator. -/
theorem s2v_l1b_coordinate_action_descends_as_power
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) (hn : 0 < n) (q : g3_power Y n ⟶ W) (d : W ⟶ W)
    (hinv : ∀ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
      ∑ j, v j = 0 → s2_action S Y a e n v τ ≫ q = q)
    (hgen : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q)
    (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n))
    (k : ℕ) (hk : (k : ZMod S.m) = ∑ j, v j) :
    s2_action S Y a e n v τ ≫ q = q ≫ (End.of d ^ k).asHom := by
  let w := fun j => v j - s2_delta S n hn (k : ZMod S.m) j
  have hw : ∑ j, w j = 0 := by
    dsimp only [w]
    rw [Finset.sum_sub_distrib]
    have hd : ∑ j, s2_delta S n hn (k : ZMod S.m) j = (k : ZMod S.m) := by
      simp [s2_delta]
    rw [hd, hk, sub_self]
  have he : (fun j => s2_delta S n hn (k : ZMod S.m) j +
      w ((1 : Equiv.Perm (Fin n)).symm j)) = v := by
    funext j
    simp only [Equiv.Perm.one_symm, Equiv.Perm.one_apply, w, add_sub_cancel]
  have hcomp : s2_action S Y a e n w τ ≫
      s2_action S Y a e n (s2_delta S n hn (k : ZMod S.m)) 1 =
      s2_action S Y a e n v τ := by
    rw [(s2_coordinateAction_laws S Y a e ha1 hamul n).2, he, one_mul]
  rw [← hcomp, Category.assoc,
    ← s2v_l1b_residual_generator_powers S Y W a e ha1 hamul n hn q d hgen,
    ← Category.assoc, hinv w τ hw]

/-- A full coordinate quotient factors through the retained residual generator's categorical quotient. -/
theorem s2v_l1b_residual_categorical_quotient
    (S : g32p_Supplier) (Y W B : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) (hn : 0 < n) (q : g3_power Y n ⟶ W) [Epi q]
    (β : W ⟶ B) (d : W ⟶ W)
    (hinv : ∀ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
      ∑ j, v j = 0 → s2_action S Y a e n v τ ≫ q = q)
    (hgen : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q)
    (hfull : ∀ (T : Over (Spec ↧ℂ)) (g : g3_power Y n ⟶ T),
      (∀ v τ, s2_action S Y a e n v τ ≫ g = g) →
      ∃! u : B ⟶ T, (q ≫ β) ≫ u = g) :
    ∀ (T : Over (Spec ↧ℂ)) (g : W ⟶ T), d ≫ g = g →
      ∃! u : B ⟶ T, β ≫ u = g := by
  intro T g hg
  have hp : ∀ k : ℕ, (End.of d ^ k).asHom ≫ g = g := by
    intro k
    induction k with
    | zero => simp only [pow_zero, End.one_def, Category.id_comp]
    | succ k ih =>
      rw [pow_succ, End.mul_asHom]
      change (d ≫ (End.of d ^ k).asHom) ≫ g = g
      rw [Category.assoc, ih, hg]
  have hi : ∀ v τ, s2_action S Y a e n v τ ≫ (q ≫ g) = q ≫ g := by
    intro v τ
    rw [← Category.assoc,
      s2v_l1b_coordinate_action_descends_as_power S Y W a e ha1 hamul n hn q d hinv hgen
        v τ (∑ j, v j).val (ZMod.natCast_zmod_val _), Category.assoc, hp]
  obtain ⟨u, hu, huniq⟩ := hfull T (q ≫ g) hi
  refine ⟨u, ?_, ?_⟩
  · apply (cancel_epi q).mp
    simpa only [Category.assoc] using hu
  · intro u' hu'
    apply huniq u'
    rw [Category.assoc, hu']

end HodgeLean.Foundations.Program

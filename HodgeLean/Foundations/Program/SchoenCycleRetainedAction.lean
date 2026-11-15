import HodgeLean.Foundations.Program.SchoenCycleSymmetricPoints

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The retained translations and permutations, with the zero-sum equation.
Source: Schoen (1988), section 1, printed pp. 5–6. -/
structure s2e_Retained (m h : ℕ) where
  vector : Fin h → ZMod m
  zero_sum : ∑ i, vector i = 0
  perm : Equiv.Perm (Fin h)

@[ext] theorem s2e_Retained.ext {m h : ℕ} (x y : s2e_Retained m h)
    (hv : x.vector = y.vector) (hp : x.perm = y.perm) : x = y := by
  cases x; cases y; cases hv; cases hp; rfl

instance {m h : ℕ} : Group (s2e_Retained m h) where
  one := ⟨0, by simp, 1⟩
  mul x y := ⟨fun i => x.vector i + y.vector (x.perm.symm i), by
    rw [Finset.sum_add_distrib, Equiv.sum_comp x.perm.symm, x.zero_sum, y.zero_sum, add_zero],
    x.perm * y.perm⟩
  inv x := ⟨fun i => -x.vector (x.perm i), by
    rw [Finset.sum_neg_distrib, Equiv.sum_comp x.perm, x.zero_sum, neg_zero], x.perm⁻¹⟩
  mul_assoc x y z := by
    apply s2e_Retained.ext
    · funext i
      exact add_assoc _ _ _
    · exact mul_assoc _ _ _
  one_mul x := by
    apply s2e_Retained.ext
    · funext i; exact zero_add _
    · exact one_mul _
  mul_one x := by
    apply s2e_Retained.ext
    · funext i; exact add_zero _
    · exact mul_one _
  inv_mul_cancel x := by
    apply s2e_Retained.ext
    · funext i
      change -x.vector (x.perm i) + x.vector (x.perm i) = 0
      exact neg_add_cancel _
    · exact inv_mul_cancel _

instance {m h : ℕ} [NeZero m] : Fintype (s2e_Retained m h) :=
  Fintype.ofInjective (fun x => (x.vector, x.perm)) (by
    intro x y hxy
    exact s2e_Retained.ext x y (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))

/-- Identity and composition for the specified coordinate action.
Source: Schoen (1988), section 1, printed pp. 5–6. -/
theorem s2e_retained_coordinate_laws (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (h : ℕ) :
    s2_action S Y a e h 0 1 = 𝟙 (g3_power Y h) ∧
    ∀ (v w : Fin h → ZMod S.m) (σ τ : Equiv.Perm (Fin h)),
      s2_action S Y a e h v σ ≫ s2_action S Y a e h w τ =
        s2_action S Y a e h (fun i => w i + v (τ.symm i)) (τ * σ) := by
  have hc (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)) (i : Fin h) :
      s2_action S Y a e h v σ ≫ g3_proj Y h i =
        g3_proj Y h (σ.symm i) ≫ a (e.symm (.ofAdd (v i))) := s2_check_lift_proj _ _ _
  constructor
  · apply s2e_power_hom_ext h
    intro i
    rw [hc]
    simp only [Pi.zero_apply, ofAdd_zero, map_one, ha1,
      Category.comp_id, Category.id_comp]
    rfl
  · intro v w σ τ
    apply s2e_power_hom_ext h
    intro i
    rw [Category.assoc, hc, ← Category.assoc, hc, Category.assoc, hc]
    rw [ofAdd_add, map_mul, hamul]
    rfl

/-- Realize each retained element by the specified scheme automorphism.
Source: Schoen (1988), section 1, printed pp. 5–6. -/
def s2e_retainedAction (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m)) (h : ℕ)
    (g : s2e_Retained S.m h) : g3_power Y h ⟶ g3_power Y h :=
  s2_action S Y a e h g.vector g.perm

/-- The realization has the action order used by rational quotient comparison.
Source: Schoen (1988), section 1, printed pp. 5–6. -/
theorem s2e_retainedAction_laws (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (h : ℕ) :
    s2e_retainedAction S Y a e h 1 = 𝟙 _ ∧
    ∀ u v, s2e_retainedAction S Y a e h (u * v) =
      s2e_retainedAction S Y a e h v ≫ s2e_retainedAction S Y a e h u := by
  obtain ⟨h1, hmul⟩ := s2e_retained_coordinate_laws S Y a e ha1 hamul h
  exact ⟨h1, fun u v => (hmul v.vector u.vector v.perm u.perm).symm⟩

/-- Group-indexed quantification is exactly the retained vector/permutation quantification.
Source: Schoen (1988), section 1, printed pp. 5–6. -/
theorem s2e_retained_quantifiers (m h : ℕ)
    (P : (Fin h → ZMod m) → Equiv.Perm (Fin h) → Prop) :
    (∀ g : s2e_Retained m h, P g.vector g.perm) ↔
      ∀ v σ, ∑ i, v i = 0 → P v σ := by
  constructor
  · intro H v σ hv
    exact H ⟨v, hv, σ⟩
  · intro H g
    exact H g.vector g.perm g.zero_sum

end HodgeLean.Foundations.Program

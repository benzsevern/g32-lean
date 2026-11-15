import HodgeLean.Foundations.Program.SchoenTowerBranchDescent
import Mathlib.GroupTheory.Perm.Fin

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Reset one coordinate of an actual retained power to the selected point.
Source: Schoen (1988), printed p. 12, point insertion and factor projections. -/
def s2t_pointReset (C : Over (Spec ↧ℂ)) (n : ℕ) (b : ComplexPoint C) (i : Fin n) :
    g3_power C n ⟶ g3_power C n :=
  s2_lift n (fun k => if k = i then CartesianMonoidalCategory.toUnit _ ≫ b else g3_proj C n k)

/-- Drop the selected coordinate, swapping it with the first slot before projection.
Source: Schoen (1988), printed p. 12, point insertion and factor projections. -/
def s2t_dropCoordinate (C : Over (Spec ↧ℂ)) (n : ℕ) (i : Fin (n + 1)) :
    g3_power C (n + 1) ⟶ g3_power C n :=
  s2_lift n (fun k => g3_proj C (n + 1) (Equiv.swap 0 i k.succ))

@[reassoc]
theorem s2t_pointReset_proj (C : Over (Spec ↧ℂ)) (n : ℕ) (b : ComplexPoint C)
    (i k : Fin n) : s2t_pointReset C n b i ≫ g3_proj C n k =
      if k = i then CartesianMonoidalCategory.toUnit _ ≫ b else g3_proj C n k :=
  s2_check_lift_proj _ _ _

@[reassoc]
theorem s2t_dropCoordinate_proj (C : Over (Spec ↧ℂ)) (n : ℕ)
    (i : Fin (n + 1)) (k : Fin n) :
    s2t_dropCoordinate C n i ≫ g3_proj C n k =
      g3_proj C (n + 1) (Equiv.swap 0 i k.succ) := s2_check_lift_proj _ _ _

@[reassoc]
theorem s2t_comp_toUnit {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) :
    f ≫ CartesianMonoidalCategory.toUnit Y = CartesianMonoidalCategory.toUnit X :=
  Subsingleton.elim _ _

/-- The coordinate resets commute as actual scheme maps. -/
theorem s2t_pointReset_comm (C : Over (Spec ↧ℂ)) (n : ℕ) (b : ComplexPoint C)
    (i j : Fin n) :
    s2t_pointReset C n b i ≫ s2t_pointReset C n b j =
      s2t_pointReset C n b j ≫ s2t_pointReset C n b i := by
  apply s2_product_hom_ext n
  intro k
  by_cases hki : k = i
  · by_cases hkj : k = j
    · simp only [Category.assoc, s2t_pointReset_proj, if_pos hki, if_pos hkj,
        s2t_comp_toUnit_assoc]
    · simp only [Category.assoc, s2t_pointReset_proj, if_pos hki, if_neg hkj,
        s2t_comp_toUnit_assoc]
  · by_cases hkj : k = j
    · simp only [Category.assoc, s2t_pointReset_proj, if_neg hki, if_pos hkj,
        s2t_comp_toUnit_assoc]
    · simp only [Category.assoc, s2t_pointReset_proj, if_neg hki, if_neg hkj,
        s2t_comp_toUnit_assoc]

/-- Each coordinate reset is idempotent. -/
theorem s2t_pointReset_idem (C : Over (Spec ↧ℂ)) (n : ℕ) (b : ComplexPoint C)
    (i : Fin n) :
    s2t_pointReset C n b i ≫ s2t_pointReset C n b i = s2t_pointReset C n b i := by
  apply s2_product_hom_ext n
  intro k
  by_cases hk : k = i <;>
    simp only [Category.assoc, s2t_pointReset_proj, hk, ite_true, ite_false,
      s2t_comp_toUnit_assoc]

/-- Dropping a coordinate forgets its reset. -/
theorem s2t_pointReset_drop (C : Over (Spec ↧ℂ)) (n : ℕ) (b : ComplexPoint C)
    (i : Fin (n + 1)) :
    s2t_pointReset C (n + 1) b i ≫ s2t_dropCoordinate C n i = s2t_dropCoordinate C n i := by
  apply s2_product_hom_ext n
  intro k
  have hk : Equiv.swap 0 i k.succ ≠ i := by
    intro he
    have := congrArg (Equiv.swap 0 i) he
    exact Fin.succ_ne_zero k (by
      simpa only [Equiv.swap_apply_self, Equiv.swap_apply_right] using this)
  simp only [Category.assoc, s2t_dropCoordinate_proj, s2t_pointReset_proj, hk, ite_false]

/-- Any factor permutation fixing zero restricts to the remaining factors. -/
theorem s2t_perm_fix_zero_restrict (n : ℕ) (τ : Equiv.Perm (Fin (n + 1)))
    (hτ : τ 0 = 0) : ∃ σ : Equiv.Perm (Fin n), ∀ k, τ k.succ = (σ k).succ := by
  obtain ⟨⟨p, σ⟩, he⟩ := Equiv.Perm.decomposeFin.symm.surjective τ
  have hp : p = 0 := by
    simpa only [← he, Equiv.Perm.decomposeFin_symm_apply_zero] using hτ
  subst p
  refine ⟨σ, ?_⟩
  intro k
  rw [← he, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]

/-- Dropping two distinct coordinates after resetting one gives the same remaining tuple
up to an actual permutation. -/
theorem s2t_pointReset_drop_permute (C : Over (Spec ↧ℂ)) (n : ℕ) (b : ComplexPoint C)
    (i j : Fin (n + 1)) :
    ∃ σ : Equiv.Perm (Fin n),
      s2t_pointReset C (n + 1) b i ≫ s2t_dropCoordinate C n j =
        s2t_pointReset C (n + 1) b j ≫ s2t_dropCoordinate C n i ≫ s2_permute C n σ := by
  let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j * Equiv.swap i j * Equiv.swap 0 i
  have hτ : τ 0 = 0 := by simp only [τ, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  obtain ⟨σ, hσ⟩ := s2t_perm_fix_zero_restrict n τ hτ
  refine ⟨σ, ?_⟩
  apply s2_product_hom_ext n
  intro k
  have hc : Equiv.swap 0 i (σ.symm k).succ = Equiv.swap i j (Equiv.swap 0 j k.succ) := by
    have he := congrArg (fun x => Equiv.swap i j (Equiv.swap 0 j x)) (hσ (σ.symm k))
    simpa only [τ, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
      Equiv.swap_apply_self] using he
  have hne : Equiv.swap 0 j k.succ ≠ j := by
    intro he
    have := congrArg (Equiv.swap 0 j) he
    exact Fin.succ_ne_zero k (by
      simpa only [Equiv.swap_apply_self, Equiv.swap_apply_right] using this)
  simp only [Category.assoc, s2_permute, s2_check_lift_proj, s2t_dropCoordinate_proj,
    s2t_pointReset_proj, hc]
  by_cases he : Equiv.swap 0 j k.succ = i
  · simp only [he, Equiv.swap_apply_left, ite_true]
  · rw [Equiv.swap_apply_of_ne_of_ne he hne]
    simp only [he, hne, ite_false]

/-- Coordinate resets intertwine the actual factor permutations. -/
theorem s2t_permute_pointReset (C : Over (Spec ↧ℂ)) (n : ℕ) (b : ComplexPoint C)
    (i : Fin n) (σ : Equiv.Perm (Fin n)) :
    s2_permute C n σ ≫ s2t_pointReset C n b i =
      s2t_pointReset C n b (σ.symm i) ≫ s2_permute C n σ := by
  apply s2_product_hom_ext n
  intro k
  simp only [Category.assoc, s2_permute, s2_check_lift_proj, s2t_pointReset_proj,
    σ.symm.injective.eq_iff]
  by_cases hk : k = i
  · simp only [ite_eq_left hk, s2t_comp_toUnit_assoc]
  · simp only [ite_eq_right hk, s2_check_lift_proj]

/-- Dropping a coordinate intertwines permutations up to a permutation of the remaining factors. -/
theorem s2t_permute_dropCoordinate (C : Over (Spec ↧ℂ)) (n : ℕ)
    (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) :
    ∃ τ : Equiv.Perm (Fin n), s2_permute C (n + 1) σ ≫ s2t_dropCoordinate C n i =
      s2t_dropCoordinate C n (σ.symm i) ≫ s2_permute C n τ := by
  let υ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i * σ * Equiv.swap 0 (σ.symm i)
  have hυ : υ 0 = 0 := by
    simp only [υ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply,
      Equiv.swap_apply_right]
  obtain ⟨τ, hτ⟩ := s2t_perm_fix_zero_restrict n υ hυ
  refine ⟨τ, ?_⟩
  apply s2_product_hom_ext n
  intro k
  have hc : Equiv.swap 0 (σ.symm i) (τ.symm k).succ =
      σ.symm (Equiv.swap 0 i k.succ) := by
    have he := congrArg (fun x => σ.symm (Equiv.swap 0 i x)) (hτ (τ.symm k))
    simpa only [υ, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
      Equiv.swap_apply_self, Equiv.symm_apply_apply] using he
  simp only [Category.assoc, s2_permute, s2_check_lift_proj, s2t_dropCoordinate_proj, hc]

/-- Dropping the inserted first point is the identity on the original tuple. -/
theorem s2t_branchInsertion_drop (C : Over (Spec ↧ℂ)) (n : ℕ) (b : ComplexPoint C) :
    s2c_branchInsertion C n b ≫ s2t_dropCoordinate C n 0 = 𝟙 (g3_power C n) := by
  apply s2_product_hom_ext n
  intro k
  simp only [Category.assoc, s2t_dropCoordinate_proj, Equiv.swap_self,
    Equiv.refl_apply, s2c_branchInsertion, s2_check_lift_proj, Fin.cases_succ,
    Category.id_comp]

/-- Dropping and reinserting the first point is precisely its coordinate reset. -/
theorem s2t_drop_branchInsertion (C : Over (Spec ↧ℂ)) (n : ℕ) (b : ComplexPoint C) :
    s2t_dropCoordinate C n 0 ≫ s2c_branchInsertion C n b =
      s2t_pointReset C (n + 1) b 0 := by
  apply s2_product_hom_ext (n + 1)
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Category.assoc, s2c_branchInsertion, s2_check_lift_proj, Fin.cases_zero,
      s2t_pointReset_proj, ite_true, s2t_comp_toUnit_assoc]
  · simp only [Category.assoc, s2c_branchInsertion, s2_check_lift_proj, Fin.cases_succ,
      s2t_pointReset_proj, Fin.succ_ne_zero, ite_false, s2t_dropCoordinate_proj,
      Equiv.swap_self, Equiv.refl_apply]

example (C : Over (Spec ↧ℂ)) (n : ℕ) (b : ComplexPoint C) (i k : Fin n) :
    s2t_pointReset C n b i ≫ g3_proj C n k =
      if k = i then CartesianMonoidalCategory.toUnit _ ≫ b else g3_proj C n k :=
  s2t_pointReset_proj C n b i k

example (C : Over (Spec ↧ℂ)) (n : ℕ) (i : Fin (n + 1)) (k : Fin n) :
    s2t_dropCoordinate C n i ≫ g3_proj C n k =
      g3_proj C (n + 1) (Equiv.swap 0 i k.succ) := s2t_dropCoordinate_proj C n i k

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32ContractionDefs

/-! # The maps between `A_ρ × B` and `J^{r+1}`

Homomorphism properties and factor compatibilities of the factorwise maps `g32c_lift` and
`g32c_lower`, multiplication maps on products, and the retraction `ι₀ ≫ π = [N₀]` with its
effect on cohomology. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

section Hom

theorem g32c_isMonHom_pow {X M : Over (Spec ↧ℂ)} [MonObj X] [MonObj M] [IsCommMonObj M]
    (f : X ⟶ M) [IsMonHom f] (n : ℕ) : IsMonHom (f ^ n) := by
  induction n with
  | zero => rw [pow_zero, Hom.one_def]; infer_instance
  | succ n ih => rw [pow_succ, Hom.mul_def]; infer_instance

theorem g32c_comp_pow_retract {P J : Over (Spec ↧ℂ)} [MonObj P] (f : P ⟶ J) (p : J ⟶ P)
    {N N₀ : ℕ} (hfp : f ≫ p = 𝟙 P ^ N) (hN : N ∣ N₀) : f ≫ p ≫ 𝟙 P ^ (N₀ / N) = 𝟙 P ^ N₀ := by
  rw [← Category.assoc, hfp, MonObj.comp_pow, Category.comp_id, ← pow_mul, Nat.mul_div_cancel' hN]

theorem g32c_tensor_one_pow {A B : Over (Spec ↧ℂ)} [MonObj A] [MonObj B] (n : ℕ) :
    (𝟙 A ^ n) ⊗ₘ (𝟙 B ^ n) = 𝟙 (A ⊗ B) ^ n := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [tensorHom_fst, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · rw [tensorHom_snd, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]

end Hom

section Lift

variable (J : Over (Spec ↧ℂ))

theorem g32c_lift_proj : ∀ (r : ℕ) (F : Fin r → Over (Spec ↧ℂ)) (f : ∀ i, F i ⟶ J) (i : Fin r),
    g32c_lift J r F f ≫ g3_proj J r i = cfd_proj r F i ≫ f i
  | 0, _, _, i => i.elim0
  | r + 1, F, f, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact tensorHom_fst _ _
    · change (f 0 ⊗ₘ g32c_lift J r (fun i => F i.succ) (fun i => f i.succ)) ≫
          snd J (g3_power J r) ≫ g3_proj J r j = (snd _ _ ≫ cfd_proj r (fun k => F k.succ) j) ≫ _
      rw [tensorHom_snd_assoc, g32c_lift_proj r _ _ j, Category.assoc]

theorem g32c_lower_proj : ∀ (r : ℕ) (F : Fin r → Over (Spec ↧ℂ)) (p : ∀ i, J ⟶ F i) (i : Fin r),
    g32c_lower J r F p ≫ cfd_proj r F i = g3_proj J r i ≫ p i
  | 0, _, _, i => i.elim0
  | r + 1, F, p, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact tensorHom_fst _ _
    · change (p 0 ⊗ₘ g32c_lower J r (fun i => F i.succ) (fun i => p i.succ)) ≫
          snd (F 0) (cfd_product r fun k => F k.succ) ≫ cfd_proj r (fun k => F k.succ) j =
            (snd _ _ ≫ g3_proj J r j) ≫ _
      rw [tensorHom_snd_assoc, g32c_lower_proj r _ _ j, Category.assoc]

variable [GrpObj J]

theorem g32c_lift_isMonHom : ∀ (r : ℕ) (F : Fin r → Over (Spec ↧ℂ)) [∀ i, GrpObj (F i)]
    (f : ∀ i, F i ⟶ J), (∀ i, IsMonHom (f i)) → IsMonHom (g32c_lift J r F f)
  | 0, _, _, _, _ => inferInstanceAs (IsMonHom (𝟙 (𝟙_ (Over (Spec ↧ℂ)))))
  | r + 1, F, _, f, hf => by
    have := g32c_lift_isMonHom r (fun i => F i.succ) (fun i => f i.succ) fun i => hf i.succ
    have := hf 0
    exact inferInstanceAs
      (IsMonHom (f 0 ⊗ₘ g32c_lift J r (fun i => F i.succ) (fun i => f i.succ)))

theorem g32c_lower_isMonHom : ∀ (r : ℕ) (F : Fin r → Over (Spec ↧ℂ)) [∀ i, GrpObj (F i)]
    (p : ∀ i, J ⟶ F i), (∀ i, IsMonHom (p i)) → IsMonHom (g32c_lower J r F p)
  | 0, _, _, _, _ => inferInstanceAs (IsMonHom (𝟙 (𝟙_ (Over (Spec ↧ℂ)))))
  | r + 1, F, _, p, hp => by
    have := g32c_lower_isMonHom r (fun i => F i.succ) (fun i => p i.succ) fun i => hp i.succ
    have := hp 0
    exact inferInstanceAs
      (IsMonHom (p 0 ⊗ₘ g32c_lower J r (fun i => F i.succ) (fun i => p i.succ)))

omit [GrpObj J] in
theorem g32c_lift_lower : ∀ (r : ℕ) (F : Fin r → Over (Spec ↧ℂ)) [∀ i, GrpObj (F i)]
    (f : ∀ i, F i ⟶ J) (p : ∀ i, J ⟶ F i) (N : ℕ), (∀ i, f i ≫ p i = 𝟙 (F i) ^ N) →
    g32c_lift J r F f ≫ g32c_lower J r F p = 𝟙 (cfd_product r F) ^ N
  | 0, _, _, _, _, _, _ => SemiCartesianMonoidalCategory.toUnit_unique _ _
  | r + 1, F, _, f, p, N, h => by
    change (f 0 ⊗ₘ g32c_lift J r (fun i => F i.succ) (fun i => f i.succ)) ≫
      (p 0 ⊗ₘ g32c_lower J r (fun i => F i.succ) (fun i => p i.succ)) = _
    rw [tensorHom_comp_tensorHom, h 0,
      g32c_lift_lower r (fun i => F i.succ) _ _ N fun i => h i.succ]
    exact g32c_tensor_one_pow N

end Lift

variable {A : g32t_Sixfold}

theorem g32c_realization_main (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    IsMonHom (g32c_incl X S hS) ∧ IsMonHom (g32c_proj X S hS) ∧
    g32c_incl X S hS ≫ g3_proj X.J (r + 1) 0 = fst A.X (g32c_B X S hS) ≫ X.inclA ∧
    (∀ j : Fin r, g32c_incl X S hS ≫ g3_proj X.J (r + 1) j.succ =
      snd A.X (g32c_B X S hS) ≫ cfd_proj r (g32c_parts X S hS) j ≫
        (X.part (S j) (hS j)).incl) ∧
    g32c_proj X S hS ≫ fst A.X (g32c_B X S hS) =
      g3_proj X.J (r + 1) 0 ≫ X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA) ∧
    (∀ j : Fin r, g32c_proj X S hS ≫ snd A.X (g32c_B X S hS) ≫
        cfd_proj r (g32c_parts X S hS) j =
      g3_proj X.J (r + 1) j.succ ≫ (X.part (S j) (hS j)).proj ≫
        𝟙 (g32c_parts X S hS j) ^ (g32c_N X S hS / (X.part (S j) (hS j)).N)) := by
  have := X.inclA_hom
  have := X.projA_hom
  let L := g32c_lift X.J r (g32c_parts X S hS) fun j => (X.part (S j) (hS j)).incl
  let pA := X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA)
  let p : ∀ j, X.J ⟶ g32c_parts X S hS j := fun j =>
    (X.part (S j) (hS j)).proj ≫ 𝟙 (g32c_parts X S hS j) ^
      (g32c_N X S hS / (X.part (S j) (hS j)).N)
  let Lw := g32c_lower X.J r (g32c_parts X S hS) p
  refine ⟨?_, ?_, tensorHom_fst _ _, fun j => ?_, ?_, fun j => ?_⟩
  · have := g32c_lift_isMonHom X.J r (g32c_parts X S hS) _
      fun j => (X.part (S j) (hS j)).incl_hom
    exact inferInstanceAs (IsMonHom (X.inclA ⊗ₘ L))
  · have := g32c_isMonHom_pow (𝟙 A.X) (g32c_N X S hS / X.NA)
    have := g32c_lower_isMonHom X.J r (g32c_parts X S hS) p fun j => by
      have := (X.part (S j) (hS j)).proj_hom
      have := g32c_isMonHom_pow (𝟙 (g32c_parts X S hS j)) (g32c_N X S hS / (X.part (S j) (hS j)).N)
      exact inferInstanceAs (IsMonHom ((X.part (S j) (hS j)).proj ≫ 𝟙 (g32c_parts X S hS j) ^
        (g32c_N X S hS / (X.part (S j) (hS j)).N)))
    exact inferInstanceAs (IsMonHom (pA ⊗ₘ Lw))
  · change (X.inclA ⊗ₘ L) ≫ snd X.J (g3_power X.J r) ≫ g3_proj X.J r j = _
    rw [tensorHom_snd_assoc, g32c_lift_proj]
  · exact tensorHom_fst _ _
  · change (pA ⊗ₘ Lw) ≫ snd A.X (g32c_B X S hS) ≫ cfd_proj r (g32c_parts X S hS) j =
      (snd X.J (g3_power X.J r) ≫ g3_proj X.J r j) ≫ p j
    rw [tensorHom_snd_assoc, g32c_lower_proj, Category.assoc]

theorem g32c_retraction_main (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    0 < g32c_N X S hS ∧
    g32c_incl X S hS ≫ g32c_proj X S hS = 𝟙 (A.X ⊗ g32c_B X S hS) ^ g32c_N X S hS ∧
    ∀ n, homPullback (g32c_incl X S hS) n ∘ₗ homPullback (g32c_proj X S hS) n =
      ((g32c_N X S hS : ℚ) ^ n) • LinearMap.id := by
  have hpos : 0 < g32c_N X S hS :=
    Nat.mul_pos X.NA_pos (Finset.prod_pos fun j _ => (X.part (S j) (hS j)).N_pos)
  let L := g32c_lift X.J r (g32c_parts X S hS) fun j => (X.part (S j) (hS j)).incl
  let pA := X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA)
  let p : ∀ j, X.J ⟶ g32c_parts X S hS j := fun j =>
    (X.part (S j) (hS j)).proj ≫ 𝟙 (g32c_parts X S hS j) ^
      (g32c_N X S hS / (X.part (S j) (hS j)).N)
  let Lw := g32c_lower X.J r (g32c_parts X S hS) p
  have hcomp : g32c_incl X S hS ≫ g32c_proj X S hS =
      𝟙 (A.X ⊗ g32c_B X S hS) ^ g32c_N X S hS := by
    change (X.inclA ⊗ₘ L) ≫ (pA ⊗ₘ Lw) = _
    have hA : X.inclA ≫ pA = 𝟙 A.X ^ g32c_N X S hS :=
      g32c_comp_pow_retract _ _ X.retractA (dvd_mul_right _ _)
    have hp : ∀ j, (X.part (S j) (hS j)).incl ≫ p j = 𝟙 (g32c_parts X S hS j) ^ g32c_N X S hS :=
      fun j => g32c_comp_pow_retract _ _ (X.part (S j) (hS j)).retract
        (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _)
    rw [tensorHom_comp_tensorHom, hA,
      g32c_lift_lower X.J r (g32c_parts X S hS) _ _ (g32c_N X S hS) hp]
    exact g32c_tensor_one_pow _
  refine ⟨hpos, hcomp, fun n => ?_⟩
  rw [← spec_homPullback_comp, hcomp, ← zpow_natCast, spec_homPullback_zpow_degree,
    spec_homPullback_id, Int.cast_natCast]

end HodgeLean.Foundations.Program

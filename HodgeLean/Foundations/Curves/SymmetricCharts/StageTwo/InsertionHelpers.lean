import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Defs
import HodgeLean.Foundations.Program.SchoenTowerBranchProjective
import HodgeLean.Foundations.Program.SchoenTowerBranchKernel

/-! # Successive insertions of a finite ordered family

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000

/-- Recursively prepend the specified curve points to the residual power.
Source: Milne, Jacobian Varieties, §3, addition of effective divisors.
HC no distance; AV milestone no distance.
-/
def recursiveInsertion (C : Over (Spec ↧ℂ)) (m : ℕ) :
    (k : ℕ) → (Fin k → ComplexPoint C) → (g3_power C m ⟶ g3_power C (m+k))
  | 0, _ => 𝟙 _
  | k+1, b => recursiveInsertion C m k (fun i => b i.succ) ≫
      s2c_branchInsertion C (m+k) (b 0)

/-- Successive point insertions descend to an immersion of the retained quotient family.
Source: Milne, Jacobian Varieties, §3; Schoen (1988), Lemma 2.2.
HC no distance; AV milestone no distance.
-/
theorem recursive_addition (C : Over (Spec ↧ℂ)) [IsIntegral C.left]
    [Smooth C.hom] [IsProjective C.hom]
    (B : ℕ → Over (Spec ↧ℂ)) (π : ∀ n, g3_power C n ⟶ B n)
    (hinv : ∀ n σ, s2_permute C n σ ≫ π n = π n)
    (huniv : ∀ n (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : B n ⟶ T, π n ≫ d = f)
    (m k : ℕ) (b : Fin k → ComplexPoint C) :
    ∃ a : B m ⟶ B (m+k), IsClosedImmersion a.left ∧
      π m ≫ a = recursiveInsertion C m k b ≫ π (m+k) := by
  induction k with
  | zero => exact ⟨𝟙 _, inferInstance, (Category.comp_id _).trans (Category.id_comp _).symm⟩
  | succ k ih =>
    obtain ⟨a, ha, hπa⟩ := ih (fun i => b i.succ)
    obtain ⟨f, hf, _, _⟩ := s2t_branch_descent_kernel C (B (m+k)) (B (m+k+1))
      (m+k) (b 0) (π (m+k)) (π (m+k+1)) (hinv (m+k)) (huniv (m+k)) (hinv (m+k+1))
    letI := ha
    letI : IsClosedImmersion f.left := s2t_branch_projective_immersion C
      (B (m+k)) (B (m+k+1)) (m+k) (b 0) (π (m+k)) (π (m+k+1))
      (hinv (m+k)) (huniv (m+k)) (hinv (m+k+1)) (huniv (m+k+1)) f hf
    refine ⟨a ≫ f, inferInstanceAs (IsClosedImmersion (a.left ≫ f.left)), ?_⟩
    rw [← Category.assoc, hπa, Category.assoc, hf]
    exact (Category.assoc _ _ _).symm

/-- The marked coordinates of recursive insertion are the specified constant point maps.
Source: Milne, Jacobian Varieties, §3, addition of effective divisors.
HC no distance; AV milestone no distance.
-/
theorem recursiveInsertion_mark (C : Over (Spec ↧ℂ)) (m k : ℕ)
    (b : Fin k → ComplexPoint C) (i : Fin k) :
    recursiveInsertion C m k b ≫ g3_proj C (m+k) ⟨i.val, by omega⟩ =
      CartesianMonoidalCategory.toUnit _ ≫ b i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · change (recursiveInsertion C m k (fun i => b i.succ) ≫
        s2c_branchInsertion C (m+k) (b 0)) ≫ g3_proj C ((m+k)+1) 0 = _
      rw [Category.assoc, s2c_branchInsertion, s2_check_lift_proj]
      change recursiveInsertion C m k (fun i => b i.succ) ≫
        (CartesianMonoidalCategory.toUnit _ ≫ b 0) = _
      rw [← Category.assoc]
      congr 1
      exact (SemiCartesianMonoidalCategory.isTerminalTensorUnit).hom_ext _ _
    · change (recursiveInsertion C m k (fun i => b i.succ) ≫
        s2c_branchInsertion C (m+k) (b 0)) ≫
          g3_proj C ((m+k)+1) (Fin.succ ⟨i.val, by omega⟩) = _
      rw [Category.assoc, s2c_branchInsertion, s2_check_lift_proj]
      exact ih (fun i => b i.succ) i

/-- The residual coordinates of recursive insertion retain their original projections.
Source: Milne, Jacobian Varieties, §3, addition of effective divisors.
HC no distance; AV milestone no distance.
-/
theorem recursiveInsertion_residual (C : Over (Spec ↧ℂ)) (m k : ℕ)
    (b : Fin k → ComplexPoint C) (i : Fin m) :
    recursiveInsertion C m k b ≫ g3_proj C (m+k) ⟨k+i.val, by omega⟩ = g3_proj C m i := by
  induction k with
  | zero =>
    rw [recursiveInsertion, Category.id_comp]
    congr 1
    exact Fin.ext (Nat.zero_add _)
  | succ k ih =>
    have hi : (⟨(k+1)+i.val, by omega⟩ : Fin (m+(k+1))) =
        (⟨k+i.val, by omega⟩ : Fin (m+k)).succ := Fin.ext (by
      change k+1+i.val = k+i.val+1
      omega)
    rw [hi]
    change (recursiveInsertion C m k (fun i => b i.succ) ≫
      s2c_branchInsertion C (m+k) (b 0)) ≫ g3_proj C ((m+k)+1)
        (Fin.succ ⟨k+i.val, by omega⟩) = _
    rw [Category.assoc, s2c_branchInsertion, s2_check_lift_proj]
    exact ih (fun i => b i.succ)

/-- Transport a coordinate projection along an equality of power degrees.
Source: CategoryTheory, equality transport for morphisms.
HC no distance; AV milestone no distance.
-/
theorem power_projection_cast (C : Over (Spec ↧ℂ)) {m n : ℕ} (h : m = n) (i : Fin n) :
    eqToHom (congrArg (g3_power C) h) ≫ g3_proj C n i =
      g3_proj C m (Fin.cast h.symm i) := by
  subst n
  exact Category.id_comp _

/-- Recursive insertion is the literal retained multiple-insertion map after degree transport.
Source: Milne, Jacobian Varieties, §3; finite product universal property.
HC no distance; AV milestone no distance.
-/
theorem recursiveInsertion_eq_multipleInsertion (C : Over (Spec ↧ℂ))
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (h k : ℕ) (hk : k ≤ h+1) (b : Fin k → ComplexPoint C) :
    recursiveInsertion C (h+1-k) k b ≫
      eqToHom (congrArg (g3_power C) (Nat.sub_add_cancel hk)) = multipleInsertion C h k hk b := by
  apply s2_product_hom_ext (h+1)
  intro i
  rw [Category.assoc, power_projection_cast]
  unfold multipleInsertion
  rw [Category.assoc, power_projection_cast, s2_check_lift_proj]
  by_cases hi : i.val < k
  · let j : Fin k := ⟨i.val, hi⟩
    have hleft : Fin.cast (Nat.add_sub_of_le hk).symm i = j.castAdd (h+1-k) := Fin.ext rfl
    rw [hleft, Fin.addCases_left]
    convert recursiveInsertion_mark C (h+1-k) k b j using 1
    congr 2
  · let j : Fin (h+1-k) := ⟨i.val-k, by omega⟩
    have hleft : Fin.cast (Nat.add_sub_of_le hk).symm i = j.natAdd k := Fin.ext (by
      change i.val = k+(i.val-k)
      omega)
    rw [hleft, Fin.addCases_right]
    convert recursiveInsertion_residual C (h+1-k) k b j using 1
    congr 2
    apply Fin.ext
    change i.val = k+(i.val-k)
    omega
  all_goals omega

/-- Projection to the actual quotient commutes with equality transport of the degree.
Source: Equality transport in the retained quotient construction.
HC no distance; AV milestone no distance.
-/
theorem symmetric_projection_cast (C : Over (Spec ↧ℂ)) [IsIntegral C.left]
    [Smooth C.hom] [IsProjective C.hom] {m n : ℕ} (h : m = n) :
    projection C m ≫ eqToHom (congrArg (symmetricPower C) h) =
      eqToHom (congrArg (g3_power C) h) ≫ projection C n := by
  subst n
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo

import HodgeLean.Foundations.Program.SchoenCycleGeometryDefs

/-! # Independent checks of the curve-power conventions
These proofs import the definitions, without importing the reserved statements.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The transposition really exchanges the first projection with the second.
Source: the binary scheme product universal property. -/
theorem s2_check_transposition (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (v : Fin 2 → ZMod S.m) :
    s2_action S Y a e 2 v (Equiv.swap 0 1) ≫ g3_proj Y 2 0 =
      g3_proj Y 2 1 ≫ a (e.symm (.ofAdd (v 0))) := by
  change CartesianMonoidalCategory.lift _ _ ≫
    CartesianMonoidalCategory.fst Y (g3_power Y 1) = _
  rw [CartesianMonoidalCategory.lift_fst]
  have hs : (Equiv.swap (0 : Fin 2) 1).symm 0 = 1 := by decide
  exact congrArg (fun i : Fin 2 =>
    g3_proj Y 2 i ≫ a (e.symm (.ofAdd (v 0)))) hs

/-- The kernel contains paired translations; a single translation need not lie in it.
Source: Schoen (1988), §1, p. 5, the sum kernel. -/
theorem s2_check_sum_kernel :
    (∑ i : Fin 2, (![6, 6] : Fin 2 → ZMod 12) i) = 0 ∧
    (∑ i : Fin 2, (![6, 0] : Fin 2 → ZMod 12) i) ≠ 0 := by
  decide

/-- Every residual translation is represented by the specified first-coordinate lift.
Source: Schoen (1988), §1, p. 5, the map δ. -/
theorem s2_check_delta_sum (S : g32p_Supplier) (h : ℕ) (hh : 0 < h)
    (t : ZMod S.m) : ∑ i, s2_delta S h hh t i = t := by
  classical
  simp [s2_delta]

/-- Evaluation of a product lift at any coordinate.
Source: the iterated scheme product universal property. -/
theorem s2_check_lift_proj {T Y : Over (Spec ↧ℂ)} (h : ℕ)
    (f : Fin h → (T ⟶ Y)) (i : Fin h) :
    s2_lift h f ≫ g3_proj Y h i = f i := by
  induction h with
  | zero => exact Fin.elim0 i
  | succ h ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact CartesianMonoidalCategory.lift_fst _ _
    · change CartesianMonoidalCategory.lift _ _ ≫
        (CartesianMonoidalCategory.snd _ _ ≫ g3_proj Y h j) = _
      rw [← Category.assoc, CartesianMonoidalCategory.lift_snd]
      exact ih _ j

/-- Three affine-line points give a nondegenerate scheme-level test of both conventions.
Source: Schoen (1988), §1, p. 5, and affine coordinates on the complex line. -/
theorem s2_check_affine_three_points :
    ∃ (Y : Over (Spec ↧ℂ)) (p : Fin 3 → ComplexPoint Y),
      Function.Injective p ∧
      let x := s2_lift 3 p
      let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
      let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
      (x ≫ s2_permute Y 3 σ) ≫ g3_proj Y 3 0 = p 2 ∧
      (x ≫ s2_permute Y 3 σ.symm) ≫ g3_proj Y 3 0 = p 1 ∧
      ((x ≫ s2_permute Y 3 σ) ≫ s2_permute Y 3 τ) ≫ g3_proj Y 3 0 = p 0 ∧
      ((x ≫ s2_permute Y 3 τ) ≫ s2_permute Y 3 σ) ≫ g3_proj Y 3 0 = p 2 := by
  let Y : Over (Spec ↧ℂ) := Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)
  let p : Fin 3 → ComplexPoint Y :=
    fun i => (affineSpaceEquiv (Fin 1)).symm (fun _ => (i.val : ℂ))
  refine ⟨Y, p, ?_, ?_⟩
  · intro i j hij
    have hc : (i.val : ℂ) = (j.val : ℂ) :=
      congrFun ((affineSpaceEquiv (Fin 1)).symm.injective hij) 0
    apply Fin.ext
    exact_mod_cast hc
  · dsimp only
    simp only [Category.assoc, s2_permute, s2_check_lift_proj]
    exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms s2_check_lift_proj
#print axioms s2_check_affine_three_points
/-- Three distinct points detect the inverse in a three-cycle.
Source: Schoen (1988), §1, p. 5, coordinate permutation convention. -/
theorem s2_check_three_cycle :
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
    let x : Fin 3 → ℕ := ![10, 20, 30]
    Function.Injective x ∧ σ ≠ σ.symm ∧
      (fun i => x (σ.symm i)) = ![30, 10, 20] ∧
      (fun i => x (σ i)) = ![20, 30, 10] := by
  decide

/-- Noncommuting permutations detect the categorical order on distinct points.
Source: Schoen (1988), §1, p. 5, semidirect coordinate action. -/
theorem s2_check_three_composition :
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
    let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let x : Fin 3 → ℕ := ![10, 20, 30]
    (fun i => x (σ.symm (τ.symm i))) = (fun i => x ((τ * σ).symm i)) ∧
      (fun i => x ((τ * σ).symm i)) = ![10, 30, 20] ∧
      (fun i => x ((σ * τ).symm i)) = ![30, 20, 10] ∧
      τ * σ ≠ σ * τ := by
  decide

/-- The actual scheme morphism has the same inverse convention in coordinate zero.
Source: the ternary scheme product universal property. -/
theorem s2_check_scheme_three_cycle (Y : Over (Spec ↧ℂ)) :
    s2_permute Y 3 (Equiv.swap 0 1 * Equiv.swap 1 2) ≫ g3_proj Y 3 0 =
      g3_proj Y 3 2 := by
  change CartesianMonoidalCategory.lift _ _ ≫
    CartesianMonoidalCategory.fst Y (g3_power Y 2) = _
  rw [CartesianMonoidalCategory.lift_fst]
  congr 1

#print axioms s2_check_three_cycle
#print axioms s2_check_three_composition
#print axioms s2_check_scheme_three_cycle
#print axioms s2_check_transposition
#print axioms s2_check_sum_kernel
#print axioms s2_check_delta_sum
end HodgeLean.Foundations.Program

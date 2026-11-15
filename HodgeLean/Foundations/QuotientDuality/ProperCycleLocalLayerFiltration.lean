import HodgeLean.Foundations.QuotientDuality.ProperCycleFiltrationPurity

/-! # Finite support localization from actual cofinal layer calculations -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Actual cofinal supported vanishing on successive layers gives vanishing through a finite closed filtration.
Source: Bredon, Sheaf Theory, second edition, II.10, localization for nested supports.
HC no distance; AV milestone no distance. -/
lemma properCycle_filtration_relative_vanishes_of_local_layers
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (B : ℕ → Closeds X) (hB0 : B 0 = ⊥) (m n : ℕ)
    (hinc : ∀ i, i < m → B i ≤ B (i + 1))
    (hlayers : ∀ i, i < m → ∀ x ∈ B (i + 1), x ∉ B i →
      ∀ V : Opens X, x ∈ V →
      ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧ ∀ j : ℕ, j ≤ n + (m - (i + 1)) →
        IsZero (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set X) (B (i + 1) : Set X)) j))
    (U : Opens X) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set X) (B m : Set X)) n) := by
  induction m generalizing n U with
  | zero =>
      rw [hB0]
      exact ModuleCat.isZero_iff_subsingleton.mpr
        (neighborhoodSupportRelativeCohomology_subsingleton X (∅ : Set X) n U
          (by intro x _; simp))
  | succ m ih =>
      have hsmall (j : ℕ) (hj : j ≤ n + 1) (V : Opens X) :
          IsZero (RelativeCohomology ℚ
            (neighborhoodSupportComplementPair (V : Set X) (B m : Set X)) j) := by
        apply ih j (fun i hi => hinc i (by omega)) ?_ V
        intro i hi x hxB hxnot Q hxQ
        obtain ⟨W, hWQ, hxW, hW⟩ := hlayers i (by omega) x hxB hxnot Q hxQ
        exact ⟨W, hWQ, hxW, fun k hk => hW k (by omega)⟩
      let O : Opens X := U ⊓ (B m).compl
      have hO : IsZero (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (O : Set X) (B (m + 1) : Set X)) n) := by
        apply a3b4a_classRelative_vanishing_of_cofinal_local_vanishing X (B (m + 1)) O n
        intro j hj x hxO V hxV
        by_cases hxB : x ∈ B (m + 1)
        · obtain ⟨W, hWV, hxW, hW⟩ := hlayers m (by omega) x hxB hxO.2 V hxV
          exact ⟨W, hWV, hxW, hW j (by omega)⟩
        · let W : Opens X := V ⊓ (B (m + 1)).compl
          refine ⟨W, inf_le_left, ⟨hxV, hxB⟩, ?_⟩
          exact ModuleCat.isZero_iff_subsingleton.mpr
            (neighborhoodSupportRelativeCohomology_subsingleton X (B (m + 1)) j W
              (fun _ hy => hy.2))
      apply ModuleCat.isZero_iff_subsingleton.mpr
      apply subsingleton_of_forall_eq (x := 0)
      intro a
      letI (V : Opens U) : ParacompactSpace V :=
        properCycle_open_paracompact_of_all_opens X U V
      have hz : ∀ j ∈ ({n, n + 1} : Finset ℕ),
          IsZero (RelativeCohomology ℚ
            (neighborhoodSupportComplementPair (U : Set X) (B m : Set X)) j) := by
        intro j hj
        apply hsmall j ?_ U
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl <;> omega
      apply a3b4a_classRelative_eq_zero_of_boundary_restriction X (B (m + 1)) (B m)
        (hinc m (by omega)) U n hz a
      exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hO) _ _

end HodgeLean.Foundations.QuotientDuality

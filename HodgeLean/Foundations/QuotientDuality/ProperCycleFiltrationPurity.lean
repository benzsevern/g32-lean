import HodgeLean.Foundations.QuotientDuality.ProperCycleAmbientPurity
import HodgeLean.Adapters.NormalConeB4aClassOpenExtension

/-! # Supported purity along a finite filtration of actual product strata -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Hereditary open paracompactness passes to opens of an actual open subspace.
Source: Munkres, Topology, sections 22 and 41, open embeddings and paracompactness under homeomorphisms.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_paracompact_of_all_opens
    (X : TopCat.{0}) [∀ W : Opens X, ParacompactSpace W]
    (U : Opens X) (V : Opens U) : ParacompactSpace V := by
  let f : V → X := fun v => v.1.1
  have hf : IsOpenEmbedding f := U.isOpen.isOpenEmbedding_subtypeVal.comp V.isOpen.isOpenEmbedding_subtypeVal
  let W : Opens X := ⟨Set.range f, hf.isOpen_range⟩
  haveI : ParacompactSpace (Set.range f) := inferInstanceAs (ParacompactSpace W)
  exact hf.isEmbedding.toHomeomorph.paracompactSpace_iff.mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Product models on successive strata and ambient concentration give supported vanishing through a finite filtration.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9, localization for nested supports.
HC no distance; AV milestone no distance. -/
lemma properCycle_ambient_filtration_relative_vanishes
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : X,
      Subsingleton (orientationGroup X j x))
    (B : ℕ → Closeds X) (hB0 : B 0 = ⊥) (m n : ℕ)
    (hinc : ∀ i, i < m → B i ≤ B (i + 1))
    (hcharts : ∀ i, i < m → ∀ x ∈ B (i + 1), x ∉ B i →
      ∀ V : Opens X, x ∈ V →
      ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧
        ∃ (r : ℕ) (Y : TopCat.{0}) (y : Y) (e : W ≃ₜ ((Fin r → ℂ) × Y)),
          (∀ w : W, (w : X) ∈ B (i + 1) ↔ (e w).2 = y) ∧
          (n + (m - (i + 1))) + 2 * r < N)
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
        obtain ⟨W, hWQ, hxW, r, Y, y, e, he, hbound⟩ :=
          hcharts i (by omega) x hxB hxnot Q hxQ
        exact ⟨W, hWQ, hxW, r, Y, y, e, he, by omega⟩
      let O : Opens X := U ⊓ (B m).compl
      have hO : IsZero (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (O : Set X) (B (m + 1) : Set X)) n) := by
        apply properCycle_ambient_product_charts_open_relative_vanishes X N hvan (B (m + 1)) n O
        intro x hxB hxO V hxV
        obtain ⟨W, hWV, hxW, r, Y, y, e, he, hbound⟩ :=
          hcharts m (by omega) x hxB hxO.2 V hxV
        exact ⟨W, hWV, hxW, r, Y, y, e, he, by omega⟩
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

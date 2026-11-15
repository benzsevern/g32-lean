import HodgeLean.Adapters.KleimanProductLocal
import HodgeLean.Adapters.KleimanProductGerms

/-! Regular test points for an actual finite family of equal-coheight supports. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every member of an injective pure finite family has a complex support
point outside the actual singular and intersection boundary of the whole family. -/
theorem s4_q3_regular_component_test_points
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (I : Type*) [Fintype I] (k : ℕ) (xs : I → X.left) (hinj : Function.Injective xs)
    (hco : ∀ i, Order.coheight (xs i) = k) :
    ∃ a : I → ComplexPoint X,
      (∀ i, a i ∈ cycleComponentAnalyticClosedSupport X (xs i)) ∧
      ∀ i, a i ∈ (ccm5_componentBoundary X (Fintype.card I)
        (xs ∘ (Fintype.equivFin I).symm)).compl := by
  classical
  let C (i : I) : Closeds X.left := ⟨closure ({xs i} : Set X.left), isClosed_closure⟩
  let B : Closeds X.left :=
    (⨆ i, cycleComponentSingularAmbientClosedFiltration X (xs i) 0) ⊔
      ⨆ i, ⨆ j, if i = j then ⊥ else C i ⊓ C j
  have hcod : ∀ z ∈ B, ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight z := by
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨i, hi⟩ := (ccm5_mem_finite_iSup _ z).mp hz
      exact ccm5_singularBoundary_coheight_lower_bound X k (xs i) z (hco i) hi
    · obtain ⟨i, hi⟩ := (ccm5_mem_finite_iSup _ z).mp hz
      obtain ⟨j, hj⟩ := (ccm5_mem_finite_iSup _ z).mp hi
      by_cases hij : i = j
      · simp only [hij, ite_true] at hj
        exact False.elim hj
      · rw [if_neg hij] at hj
        simpa only [Nat.cast_add, Nat.cast_one] using
          ccm5_intersection_coheight_lower_bound X.left k (xs i) (xs j) z
            (fun h => hij (hinj h)) (hco i) (hco j) hj.1 hj.2
  have hnot (i : I) : xs i ∉ B := by
    intro hi
    have h := hcod (xs i) hi
    rw [hco i] at h
    exact (not_le_of_gt (show (k : ℕ∞) < ((k + 1 : ℕ) : ℕ∞) by exact_mod_cast Nat.lt_succ_self k)) h
  choose a haC haB using fun i => hc9k_exists_complexPoint_closure_diff X (xs i) B (hnot i)
  refine ⟨a, haC, ?_⟩
  intro i hm
  apply haB i
  rcases (hc9k_mem_componentBoundary X _ _ (a i)).mp hm with hsing | hinter
  · obtain ⟨j, hj⟩ := hsing
    apply Or.inl
    exact (le_iSup (fun t => cycleComponentSingularAmbientClosedFiltration X (xs t) 0)
      ((Fintype.equivFin I).symm j)) hj
  · obtain ⟨j, l, hjl, hj, hl⟩ := hinter
    apply Or.inr
    apply (ccm5_mem_finite_iSup _ _).mpr
    refine ⟨(Fintype.equivFin I).symm j, ?_⟩
    apply (ccm5_mem_finite_iSup _ _).mpr
    refine ⟨(Fintype.equivFin I).symm l, ?_⟩
    have hne : (Fintype.equivFin I).symm j ≠ (Fintype.equivFin I).symm l :=
      fun h => hjl ((Fintype.equivFin I).symm.injective h)
    simpa only [if_neg hne] using (show (a i).underlying ∈ C ((Fintype.equivFin I).symm j) ⊓
      C ((Fintype.equivFin I).symm l) from ⟨hj, hl⟩)

end HodgeLean.Foundations.Program

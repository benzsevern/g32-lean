import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSupportGluing
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRelativeCoefficients

/-! Local projections of relative classes supported on finitely many points. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma finite_support_detects_zero (M : Type) [TopologicalSpace M] [T2Space M] (S : Set M)
    (hS : S.Finite) (n : ℕ)
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Sᶜ) n)
    (hc : ∀ (x : M) (hx : x ∈ S), relativeHomologyMap ℚ n
      (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hx)) c = 0) :
    c = 0 := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      have := ModuleCat.subsingleton_of_isZero
        (b6m_relativeHomology_empty_support_isZero ℚ M n)
      exact Subsingleton.elim _ _
  | @insert a S ha hS ih =>
      simp only [Set.insert_eq] at c hc ⊢
      have hvan : Subsingleton (RelativeHomology ℚ
          (TopPair.ofSubset (X := TopCat.of M) ({a} ∩ S)ᶜ) (n + 1)) := by
        have hdisj : ({a} : Set M) ∩ S = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro h
          simpa only [h] using ha
        rw [hdisj]
        exact ModuleCat.subsingleton_of_isZero
          (b6m_relativeHomology_empty_support_isZero ℚ M (n + 1))
      apply b6m_relativeMayerVietoris_injective ℚ isClosed_singleton hS.isClosed n hvan c
      · exact hc a (Set.mem_union_left _ (Set.mem_singleton a))
      · apply ih
        intro x hx
        rw [b6m_relativeHomologyMap_supportInclusion_trans]
        exact hc x (Set.mem_union_right _ hx)

lemma finite_support_subsingleton (M : Type) [TopologicalSpace M] [T2Space M]
    (S : Set M) (hS : S.Finite) (n : ℕ)
    (hlocal : ∀ x ∈ S, Subsingleton (orientationGroup (TopCat.of M) n x)) :
    Subsingleton (RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Sᶜ) n) := by
  refine ⟨fun a b => sub_eq_zero.mp (finite_support_detects_zero M S hS n (a - b) ?_)⟩
  intro x hx
  have := hlocal x hx
  exact Subsingleton.elim _ _

end HodgeLean.Foundations.QuotientDuality

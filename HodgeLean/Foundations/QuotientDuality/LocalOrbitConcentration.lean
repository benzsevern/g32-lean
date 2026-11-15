import HodgeLean.Foundations.QuotientDuality.OrientationRelativeDescent
import HodgeLean.Foundations.QuotientDuality.OrientationLocalReduction

/-! Point-local homology concentration for finite orbit spaces. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem orbit_local_homology_concentrated
    (G : Type) [Group G] [Fintype G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] [T2Space X] [PseudoMetrizableSpace X]
    [T2Space (orbitSpace G X)] [PseudoMetrizableSpace (orbitSpace G X)]
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (x : orbitSpace G X) (U : Opens (orbitSpace G X)), x ∈ U →
      ∃ V : Opens (orbitSpace G X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ)
    (hvanish : ∀ x i, i ≠ n → Subsingleton (orientationGroup X i x))
    (y : orbitSpace G X) (i : ℕ) (hi : i ≠ n) :
    Subsingleton (orientationGroup (orbitSpace G X) i y) := by
  letI := orbit_relative_vanishes G X y n i hi hvanish
  obtain ⟨hlift, _⟩ := orbit_relative_descent G X hX hY y i
  refine ⟨fun u v => ?_⟩
  obtain ⟨c, hc, _⟩ := hlift u
  obtain ⟨e, he, _⟩ := hlift v
  exact hc.symm.trans ((congrArg
    (relativeHomologyMap ℚ i (orbitComplementPairMap G X y))
    (Subsingleton.elim c e)).trans he)

theorem finite_support_class_exists (X : TopCat.{0}) [T2Space X]
    (A : Set X) (hA : A.Finite) (n : ℕ)
    (μ : ∀ x : X, orientationGroup X n x) :
    ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := X) Aᶜ) n,
      ∀ (x : X) (hx : x ∈ A), relativeHomologyMap ℚ n
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) c = μ x := by
  induction A, hA using Set.Finite.induction_on with
  | empty => exact ⟨0, fun _ hx => False.elim hx⟩
  | @insert a A ha hA ih =>
    obtain ⟨cA, hcA⟩ := ih
    have hsingle : ∀ (x : X) (hx : x ∈ ({a} : Set X)),
        relativeHomologyMap ℚ n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) (μ a) = μ x := by
      intro x hx
      have hxa : x = a := hx
      subst x
      have hm : supportInclusionPairMap X (Set.Subset.refl ({a} : Set X)) =
          𝟙 (pointComplementPair a) := by
        apply MorphismProperty.Arrow.Hom.ext <;> ext t <;> rfl
      rw [hm, relativeHomologyMap_id]
      rfl
    have hd : ∀ α : RelativeHomology ℚ
        (TopPair.ofSubset (X := X) (({a} : Set X) ∩ A)ᶜ) n,
        (∀ (x : X) (hx : x ∈ ({a} : Set X) ∩ A), relativeHomologyMap ℚ n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) α = 0) → α = 0 := by
      intro α hα
      exact finite_support_detects_zero X _ ((Set.finite_singleton a).inter_of_left A) n α hα
    simpa only [Set.singleton_union] using
      b6m_glue_local_classes ℚ n isClosed_singleton hA.isClosed μ (μ a) cA hsingle hcA hd

#print axioms finite_support_class_exists
#print axioms orbit_local_homology_concentrated
end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.QuotientDuality.OrientationFiniteSupport

/-! # Actual relative classes with prescribed values on a finite fibre -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Arbitrary actual local homology classes on a finite support have a unique relative homology lift.
Source: Hatcher, Algebraic Topology, section 2.2, excision and relative Mayer--Vietoris.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_local_classes_unique_lift
    (X : TopCat.{0}) [T2Space X] (S : Set X) (hS : S.Finite) (n : ℕ)
    (a : ∀ x : S, orientationGroup X n x.val) :
    ∃! c : RelativeHomology ℚ (TopPair.ofSubset (X := X) Sᶜ) n,
      ∀ x : S, relativeHomologyMap ℚ n
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr x.property)) c = a x := by
  classical
  have hex : ∀ (S : Set X) (hS : S.Finite)
      (a : ∀ x : S, orientationGroup X n x.val),
      ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := X) Sᶜ) n,
        ∀ x : S, relativeHomologyMap ℚ n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr x.property)) c = a x := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty =>
        intro a
        exact ⟨0, fun x => False.elim x.property⟩
    | @insert x S hx hS ih =>
        intro a
        obtain ⟨b, hb⟩ := ih (fun z => a ⟨z.val, Set.mem_insert_of_mem x z.property⟩)
        have hdisj : ({x} : Set X) ∩ S = ∅ := by
          ext z
          simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro he
          simpa only [he] using hx
        have hvan : Subsingleton (RelativeHomology ℚ
            (TopPair.ofSubset (X := X) (({x} : Set X) ∩ S)ᶜ) n) := by
          rw [hdisj]
          exact ModuleCat.subsingleton_of_isZero (b6m_relativeHomology_empty_support_isZero ℚ X n)
        obtain ⟨c, hc₁, hc₂⟩ := b6m_relativeMayerVietoris_glue ℚ isClosed_singleton hS.isClosed n
          (a ⟨x, Set.mem_insert x S⟩) b (Subsingleton.elim _ _)
        refine ⟨c, ?_⟩
        intro z
        rcases Set.mem_insert_iff.mp z.property with he | hz
        · have hz : z = ⟨x, Set.mem_insert x S⟩ := Subtype.ext he
          subst z
          exact hc₁
        · have hh := congrArg (relativeHomologyMap ℚ n
            (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hz))) hc₂
          rw [b6m_relativeHomologyMap_supportInclusion_trans] at hh
          exact hh.trans (hb ⟨z.val, hz⟩)
  obtain ⟨c, hc⟩ := hex S hS a
  refine ⟨c, hc, ?_⟩
  intro d hd
  apply sub_eq_zero.mp
  apply finite_support_detects_zero X S hS n (d - c)
  intro x hx
  rw [map_sub, hd ⟨x, hx⟩, hc ⟨x, hx⟩, sub_self]

/-- The literal projections to the points of a finite fibre form a linear equivalence on actual relative homology.
Source: Hatcher, Algebraic Topology, section 2.2, finite disjoint support excision.
HC no distance; AV milestone no distance. -/
def properCycle_finite_support_localization
    (X : TopCat.{0}) [T2Space X] (S : Set X) (hS : S.Finite) (n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset (X := X) Sᶜ) n ≃ₗ[ℚ]
      (∀ x : S, orientationGroup X n x.val) :=
  LinearEquiv.ofBijective
    (LinearMap.pi fun x : S => relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr x.property)))
    (by
      constructor
      · intro a b hab
        apply sub_eq_zero.mp
        apply finite_support_detects_zero X S hS n (a - b)
        intro x hx
        rw [map_sub, sub_eq_zero]
        exact congrFun hab ⟨x, hx⟩
      · intro a
        obtain ⟨c, hc, _⟩ := properCycle_finite_local_classes_unique_lift X S hS n a
        exact ⟨c, funext hc⟩)

/-- An actual finite-support relative class is the sum of its uniquely reconstructed point contributions.
Source: Hatcher, Algebraic Topology, section 2.2, finite support excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_support_sum_local_lifts
    (X : TopCat.{0}) [T2Space X] (S : Set X) (hS : S.Finite) [Fintype S] [DecidableEq S] (n : ℕ)
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := X) Sᶜ) n) :
    ∑ x : S, (properCycle_finite_support_localization X S hS n).symm
      (Pi.single x (relativeHomologyMap ℚ n
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr x.property)) c)) = c := by
  classical
  apply (properCycle_finite_support_localization X S hS n).injective
  rw [map_sum]
  simp only [LinearEquiv.apply_symm_apply]
  ext x
  simp only [Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, if_true]
  rfl

end HodgeLean.Foundations.QuotientDuality

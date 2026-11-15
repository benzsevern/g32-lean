import HodgeLean.RealDefs.ComplexFundamentalClassChainDefs

/-! # Small chains inside the subspace `M \ (A ∩ B)`

For closed `A`, `B ⊆ M`, the sets `M \ A`, `M \ B` form an open cover of the subspace
`M \ (A ∩ B)`. Chains small for this cover, taken in the subspace, are the chains of
`C(M \ A) + C(M \ B)` in `M`; so the small-chain theorem in the subspace makes
`relativeSumSmallChainComparison` a quasi-isomorphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

variable {M : Type} [TopologicalSpace M] (A B : Set M)

/-- The trace of `M \ A` on the subspace `M \ (A ∩ B)`.
Source: Hatcher, *Algebraic Topology*, Proposition 2.21, applied in the space `M \ (A ∩ B)`. -/
def interComplLeftCover : Set (TopCat.of ↥((A ∩ B)ᶜ)) :=
  Subtype.val ⁻¹' Aᶜ

example (y : TopCat.of ↥((A ∩ B)ᶜ)) : y ∈ interComplLeftCover A B ↔ y.1 ∉ A :=
  Iff.rfl

/-- The trace of `M \ B` on the subspace `M \ (A ∩ B)`.
Source: Hatcher, *Algebraic Topology*, Proposition 2.21, applied in the space `M \ (A ∩ B)`. -/
def interComplRightCover : Set (TopCat.of ↥((A ∩ B)ᶜ)) :=
  Subtype.val ⁻¹' Bᶜ

example (y : TopCat.of ↥((A ∩ B)ᶜ)) : y ∈ interComplRightCover A B ↔ y.1 ∉ B :=
  Iff.rfl

lemma toSSet_subsetInclusion_apply (U : Set M) {n : SimplexCategoryᵒᵖ}
    (s : (TopCat.toSSet.obj (TopCat.of ↥U)).obj n) (p) :
    (TopCat.of M).toSSetObjEquiv n
        ((TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of M) U)).app n s) p =
      ((TopCat.of ↥U).toSSetObjEquiv n s p).1 :=
  rfl

/-- Small simplices of the subspace, pushed into `M`, are the small simplices of `M`. -/
lemma interCompl_smallSubcomplex_range :
    SSet.Subcomplex.range
        ((subsetSingularSubcomplex (TopCat.of ↥((A ∩ B)ᶜ)) (interComplLeftCover A B) ⊔
            subsetSingularSubcomplex (TopCat.of ↥((A ∩ B)ᶜ)) (interComplRightCover A B)).ι ≫
          TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of M) (A ∩ B)ᶜ)) =
      subsetSingularSubcomplex (TopCat.of M) Aᶜ ⊔ subsetSingularSubcomplex (TopCat.of M) Bᶜ := by
  ext n t
  change t ∈ Set.range _ ↔ t ∈ (subsetSingularSubcomplex (TopCat.of M) Aᶜ).obj n ∨
    t ∈ (subsetSingularSubcomplex (TopCat.of M) Bᶜ).obj n
  constructor
  · rintro ⟨⟨s, hs⟩, rfl⟩
    rcases hs with hs | hs
    · left
      rw [mem_subsetSingularSubcomplex_iff] at hs ⊢
      exact fun p => hs p
    · right
      rw [mem_subsetSingularSubcomplex_iff] at hs ⊢
      exact fun p => hs p
  · intro ht
    have htW : t ∈ (subsetSingularSubcomplex (TopCat.of M) (A ∩ B)ᶜ).obj n := by
      rw [mem_subsetSingularSubcomplex_iff]
      rcases ht with ht | ht
      · rw [mem_subsetSingularSubcomplex_iff] at ht
        exact fun p h => ht p h.1
      · rw [mem_subsetSingularSubcomplex_iff] at ht
        exact fun p h => ht p h.2
    obtain ⟨s, rfl⟩ := htW
    refine ⟨⟨s, ?_⟩, rfl⟩
    rcases ht with ht | ht
    · left
      rw [mem_subsetSingularSubcomplex_iff] at ht ⊢
      exact fun p => ht p
    · right
      rw [mem_subsetSingularSubcomplex_iff] at ht ⊢
      exact fun p => ht p

private abbrev interComplSmallMap :
    TwoSubsetSmallSingularSet (TopCat.of ↥((A ∩ B)ᶜ)) (interComplLeftCover A B)
        (interComplRightCover A B) ⟶ TopCat.toSSet.obj (TopCat.of M) :=
  (subsetSingularSubcomplex (TopCat.of ↥((A ∩ B)ᶜ)) (interComplLeftCover A B) ⊔
      subsetSingularSubcomplex (TopCat.of ↥((A ∩ B)ᶜ)) (interComplRightCover A B)).ι ≫
    TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of M) (A ∩ B)ᶜ)

instance : Mono (interComplSmallMap A B) := by
  have := subsetSingularMap_mono (TopCat.of M) (A ∩ B)ᶜ
  dsimp only [interComplSmallMap]
  infer_instance

/-- The small singular set of the cover `{M \ A, M \ B}` of the subspace `M \ (A ∩ B)` is the
small singular set of `M \ A`, `M \ B` in `M`.
Source: Hatcher, *Algebraic Topology*, Proposition 2.21 (the chains `C_n^U`), applied in the
space `M \ (A ∩ B)`. -/
def interComplSmallIso :
    TwoSubsetSmallSingularSet (TopCat.of ↥((A ∩ B)ᶜ)) (interComplLeftCover A B)
        (interComplRightCover A B) ≅
      TwoSubsetSmallSingularSet (TopCat.of M) Aᶜ Bᶜ :=
  asIso (SSet.Subcomplex.toRange (interComplSmallMap A B)) ≪≫
    SSet.Subcomplex.eqToIso (interCompl_smallSubcomplex_range A B)

example : (interComplSmallIso A B).hom ≫
    (subsetSingularSubcomplex (TopCat.of M) Aᶜ ⊔ subsetSingularSubcomplex (TopCat.of M) Bᶜ).ι =
      interComplSmallMap A B :=
  rfl

lemma interComplSmallIso_hom_comp :
    (interComplSmallIso A B).hom ≫ SSet.Subcomplex.homOfLE (relativeSumSubcomplex_le M A B) ≫
        (subsetSingularIso (TopCat.of M) (A ∩ B)ᶜ).inv =
      (subsetSingularSubcomplex (TopCat.of ↥((A ∩ B)ᶜ)) (interComplLeftCover A B) ⊔
        subsetSingularSubcomplex (TopCat.of ↥((A ∩ B)ᶜ)) (interComplRightCover A B)).ι := by
  have := subsetSingularMap_mono (TopCat.of M) (A ∩ B)ᶜ
  apply (cancel_mono (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of M) (A ∩ B)ᶜ))).1
  have h : (subsetSingularIso (TopCat.of M) (A ∩ B)ᶜ).inv ≫
      TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of M) (A ∩ B)ᶜ) =
        (subsetSingularSubcomplex (TopCat.of M) (A ∩ B)ᶜ).ι := by
    rw [Iso.inv_comp_eq]; rfl
  rw [Category.assoc, Category.assoc, h, SSet.Subcomplex.homOfLE_ι]
  rfl

/-- For closed `A`, `B`, the small-chain comparison `C(M \ A) + C(M \ B) → C(M \ (A ∩ B))` is a
quasi-isomorphism. -/
theorem relativeSumSmallChainComparison_quasiIso_of_isClosed (hA : IsClosed A)
    (hB : IsClosed B) : QuasiIso (relativeSumSmallChainComparison M A B) := by
  let Y := TopCat.of ↥((A ∩ B)ᶜ)
  have hU : IsOpen (interComplLeftCover A B) :=
    hA.isOpen_compl.preimage continuous_subtype_val
  have hV : IsOpen (interComplRightCover A B) :=
    hB.isOpen_compl.preimage continuous_subtype_val
  have hUV : interComplLeftCover A B ∪ interComplRightCover A B = Set.univ :=
    Set.eq_univ_of_forall fun y => not_and_or.mp y.2
  have ha : QuasiIso (twoSubsetSmallChainInclusion Y (interComplLeftCover A B)
      (interComplRightCover A B)) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact twoSubsetSmallChainInclusion_homology_isIso Y _ _ hU hV hUV n
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  have hfac : F.map (interComplSmallIso A B).hom ≫ relativeSumSmallChainComparison M A B =
      twoSubsetSmallChainInclusion Y (interComplLeftCover A B) (interComplRightCover A B) := by
    change F.map _ ≫ F.map _ = F.map _
    rw [← F.map_comp, interComplSmallIso_hom_comp]
  have : QuasiIso (F.map (interComplSmallIso A B).hom) := quasiIso_of_isIso _
  rw [← hfac] at ha
  exact (quasiIso_iff_comp_left (hφ := this) _ _).1 ha

end HodgeLean.RealDefs

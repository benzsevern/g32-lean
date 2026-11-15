import HodgeLean.Foundations.QuotientDuality.PersistenceRangeAction
import HodgeLean.Foundations.Program.SchoenTowerDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion

/-! Actual exceptional preimages and their image-pair actions. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_point_end_order (W : Over (Spec ↧ℂ)) (d : W ⟶ W)
    (m : ℕ) (hd : End.of d ^ m = 1) :
    End.of (TopCat.ofHom (Point.continuousMap d)) ^ m = 1 := by
  let F : Over (Spec ↧ℂ) ⥤ TopCat :=
    { obj := fun X => TopCat.of (ComplexPoint X)
      map := fun f => TopCat.ofHom (Point.continuousMap f)
      map_id := by
        intro X
        apply TopCat.ext
        intro x
        exact Category.comp_id x
      map_comp := by
        intro X Y Z f g
        apply TopCat.ext
        intro x
        exact (Category.assoc x f g).symm }
  have h := congrArg (F.mapEnd W) hd
  rw [map_pow, map_one] at h
  exact h

lemma persistence_preimage_pair_lifts
    (K : Type) [Field K] [CharZero K]
    {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B)
    [IsClosedImmersion j.left]
    (d : W ⟶ W) (hd : d ≫ β = β) (m : ℕ) (hm : 0 < m)
    (horder : End.of d ^ m = 1)
    (hvan : ∀ (ζ : K), IsPrimitiveRoot ζ m → ∀ n (v : Cohomology K (TopCat.of (ComplexPoint (s2b_preimage β j))) n),
      cohomologyMap K n (TopCat.ofHom (Point.continuousMap
        (s2b_preimageDeck β j d hd))) v = ζ • v → v = 0) :
    let PX := TopPair.ofSubset (X := TopCat.of (ComplexPoint W))
      (Set.range (Point.map (s2b_toCover β j)))
    ∃ Drel : PX ⟶ PX,
      TopPair.Hom.fst Drel = TopCat.ofHom (Point.continuousMap d) ∧
      ∀ (n : ℕ) (ζ : K), IsPrimitiveRoot ζ m →
      ∀ v : Cohomology K (TopCat.of (ComplexPoint W)) n,
        cohomologyMap K n (TopCat.ofHom (Point.continuousMap d)) v = ζ • v →
        ∃! u : RelativeCohomology K PX n,
          relativeCohomologyMap K n Drel u = ζ • u ∧
          relativeCohomologyToAbsolute K PX n u = v := by
  let J := TopCat.ofHom (Point.continuousMap (s2b_toCover β j))
  let e := TopCat.ofHom (Point.continuousMap (s2b_preimageDeck β j d hd))
  let D := TopCat.ofHom (Point.continuousMap d)
  have hj : e ≫ J = J ≫ D := by
    apply TopCat.ext
    intro x
    change (x ≫ s2b_preimageDeck β j d hd) ≫ s2b_toCover β j =
      (x ≫ s2b_toCover β j) ≫ d
    have hs : s2b_preimageDeck β j d hd ≫ s2b_toCover β j = s2b_toCover β j ≫ d :=
      pullback.lift_fst _ _ _
    rw [Category.assoc, hs, Category.assoc]
  haveI : IsClosedImmersion (s2b_toCover β j).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (((IsPullback.of_hasPullback β j).map (Over.forget _)).flip) (inferInstance : IsClosedImmersion j.left)
  have hEmb : Topology.IsEmbedding J :=
    (ComplexPoint.isClosedEmbedding_map_of_closedImmersion (s2b_toCover β j)).isEmbedding
  refine ⟨persistenceRangeAction J e D hj, rfl, ?_⟩
  intro n ζ hζ v hv
  exact persistence_range_primitive_lift K J e D hj hEmb m hm
    (persistence_point_end_order W d m horder) ζ (hvan ζ hζ) n v hv

/-- The deck map on the actual exceptional image pair.
Source: Hatcher, Algebraic Topology, section 2.1, maps of pairs. -/
def persistencePreimagePairAction
    {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B)
    (d : W ⟶ W) (hd : d ≫ β = β) :
    TopPair.ofSubset (X := TopCat.of (ComplexPoint W))
      (Set.range (Point.map (s2b_toCover β j))) ⟶
    TopPair.ofSubset (X := TopCat.of (ComplexPoint W))
      (Set.range (Point.map (s2b_toCover β j))) :=
  persistenceRangeAction
    (TopCat.ofHom (Point.continuousMap (s2b_toCover β j)))
    (TopCat.ofHom (Point.continuousMap (s2b_preimageDeck β j d hd)))
    (TopCat.ofHom (Point.continuousMap d)) (by
      apply TopCat.ext
      intro x
      change (x ≫ s2b_preimageDeck β j d hd) ≫ s2b_toCover β j =
        (x ≫ s2b_toCover β j) ≫ d
      have hs : s2b_preimageDeck β j d hd ≫ s2b_toCover β j = s2b_toCover β j ≫ d :=
        pullback.lift_fst _ _ _
      rw [Category.assoc, hs, Category.assoc])

lemma persistence_preimage_pair_action_lifts
    (K : Type) [Field K] [CharZero K]
    {W B E : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B)
    [IsClosedImmersion j.left]
    (d : W ⟶ W) (hd : d ≫ β = β) (m : ℕ) (hm : 0 < m)
    (horder : End.of d ^ m = 1)
    (hvan : ∀ (ζ : K), IsPrimitiveRoot ζ m → ∀ n
      (v : Cohomology K (TopCat.of (ComplexPoint (s2b_preimage β j))) n),
      cohomologyMap K n (TopCat.ofHom (Point.continuousMap
        (s2b_preimageDeck β j d hd))) v = ζ • v → v = 0)
    (n : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ m)
    (v : Cohomology K (TopCat.of (ComplexPoint W)) n)
    (hv : cohomologyMap K n (TopCat.ofHom (Point.continuousMap d)) v = ζ • v) :
    ∃! u : RelativeCohomology K (TopPair.ofSubset (X := TopCat.of (ComplexPoint W))
      (Set.range (Point.map (s2b_toCover β j)))) n,
      relativeCohomologyMap K n (persistencePreimagePairAction β j d hd) u = ζ • u ∧
      relativeCohomologyToAbsolute K (TopPair.ofSubset (X := TopCat.of (ComplexPoint W))
        (Set.range (Point.map (s2b_toCover β j)))) n u = v := by
  obtain ⟨Drel, hDrel, hlift⟩ :=
    persistence_preimage_pair_lifts K β j d hd m hm horder hvan
  have heq : Drel = persistencePreimagePairAction β j d hd :=
    persistence_pair_end_ext hDrel
  rw [heq] at hlift
  exact hlift n ζ hζ v hv

end HodgeLean.Foundations.QuotientDuality

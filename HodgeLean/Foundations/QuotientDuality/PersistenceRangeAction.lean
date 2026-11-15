import HodgeLean.Foundations.QuotientDuality.PersistencePairSequence
import Mathlib.Topology.Homeomorph.Lemmas

/-! Pair actions on the actual image of an equivariant embedding. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The ambient action restricted to its actual invariant image pair.
Source: Hatcher, Algebraic Topology, section 2.1, maps of pairs. -/
def persistenceRangeAction {E X : TopCat.{0}}
    (j : E ⟶ X) (e : E ⟶ E) (d : X ⟶ X) (hj : e ≫ j = j ≫ d) :
    TopPair.ofSubset (Set.range j) ⟶ TopPair.ofSubset (Set.range j) :=
  TopPair.ofSubsetHom d (by
    rintro x ⟨y, rfl⟩
    exact ⟨e y, ConcreteCategory.congr_hom hj y⟩)

lemma persistence_range_subspace_vanishing
    (K : Type) [CommRing K] {E X : TopCat.{0}}
    (j : E ⟶ X) (e : E ⟶ E) (d : X ⟶ X) (hj : e ≫ j = j ≫ d)
    (hEmb : Topology.IsEmbedding j) (ζ : K)
    (hvan : ∀ n (v : Cohomology K E n), cohomologyMap K n e v = ζ • v → v = 0) :
    ∀ n (v : Cohomology K (TopPair.ofSubset (Set.range j)).snd n),
      cohomologyMap K n (TopPair.Hom.snd (persistenceRangeAction j e d hj)) v =
        ζ • v → v = 0 := by
  let H := hEmb.toHomeomorph
  let J : E ⟶ (TopPair.ofSubset (Set.range j)).snd :=
    TopCat.ofHom ⟨H, H.continuous⟩
  let I : (TopPair.ofSubset (Set.range j)).snd ⟶ E :=
    TopCat.ofHom ⟨H.symm, H.symm.continuous⟩
  have hIJ : I ≫ J = 𝟙 _ := by
    apply TopCat.ext
    exact H.apply_symm_apply
  have hJ : e ≫ J = J ≫ TopPair.Hom.snd (persistenceRangeAction j e d hj) := by
    apply TopCat.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom hj x
  intro n v hv
  have he : cohomologyMap K n e (cohomologyMap K n J v) =
      ζ • cohomologyMap K n J v := by
    have h := congrArg (cohomologyMap K n) hJ
    rw [cohomologyMap_comp, cohomologyMap_comp] at h
    change (cohomologyMap K n e).comp (cohomologyMap K n J) v = _
    rw [h]
    change cohomologyMap K n J (cohomologyMap K n
      (TopPair.Hom.snd (persistenceRangeAction j e d hj)) v) = _
    rw [hv, map_smul]
  have hz := hvan n (cohomologyMap K n J v) he
  have hh : cohomologyMap K n I (cohomologyMap K n J v) = v := by
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hIJ, cohomologyMap_id]
    rfl
  rw [hz, map_zero] at hh
  exact hh.symm

lemma persistence_range_primitive_lift
    (K : Type) [Field K] [CharZero K] {E X : TopCat.{0}}
    (j : E ⟶ X) (e : E ⟶ E) (d : X ⟶ X) (hj : e ≫ j = j ≫ d)
    (hEmb : Topology.IsEmbedding j) (m : ℕ) (hm : 0 < m)
    (hd : End.of d ^ m = 1) (ζ : K)
    (hvan : ∀ n (v : Cohomology K E n), cohomologyMap K n e v = ζ • v → v = 0)
    (n : ℕ) (v : Cohomology K X n) (hv : cohomologyMap K n d v = ζ • v) :
    ∃! u : RelativeCohomology K (TopPair.ofSubset (Set.range j)) n,
      relativeCohomologyMap K n (persistenceRangeAction j e d hj) u = ζ • u ∧
      relativeCohomologyToAbsolute K (TopPair.ofSubset (Set.range j)) n u = v := by
  exact persistence_pair_primitive_lift K _ (persistenceRangeAction j e d hj) m hm hd ζ
    (persistence_range_subspace_vanishing K j e d hj hEmb ζ hvan) n v hv

end HodgeLean.Foundations.QuotientDuality

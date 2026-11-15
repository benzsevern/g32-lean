import HodgeLean.Foundations.QuotientDuality.PersistenceSequence
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainCone
import HodgeConjecture.Mathlib.Topology.Category.TopPair
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-! The actual dual singular sequence and finite-order pair pullbacks. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_pair_end_ext {X : TopPair.{0}} {f g : X ⟶ X}
    (h : TopPair.Hom.fst f = TopPair.Hom.fst g) : f = g := by
  apply MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply (TopPair.isEmbedding_map X).injective
    exact (TopPair.Hom.w_apply f x).trans
      ((congrArg (fun t : X.fst ⟶ X.fst => t (X.map x)) h).trans
        (TopPair.Hom.w_apply g x).symm)
  · exact h

lemma persistence_pair_order (X : TopPair.{0}) (d : X ⟶ X) (m : ℕ)
    (hd : End.of (TopPair.Hom.fst d) ^ m = 1) : End.of d ^ m = 1 := by
  apply End.ext
  apply persistence_pair_end_ext
  have h := (TopPair.proj₁.mapEnd X).map_pow (End.of d) m
  change End.of (TopPair.Hom.fst ((End.of d ^ m).asHom)) = _ at h
  exact congrArg End.asHom (h.trans hd)

lemma persistence_relative_power (K : Type) [CommRing K]
    (X : TopPair.{0}) (d : X ⟶ X) (n m : ℕ) :
    relativeCohomologyMap K n ((End.of d ^ m).asHom) =
      (relativeCohomologyMap K n d) ^ m := by
  induction m with
  | zero => exact relativeCohomologyMap_id K X n
  | succ m ih =>
    rw [pow_succ]
    change relativeCohomologyMap K n (d ≫ (End.of d ^ m).asHom) = _
    rw [relativeCohomologyMap_comp, ih, pow_succ']
    rfl

lemma persistence_absolute_power (K : Type) [CommRing K]
    (X : TopCat.{0}) (d : X ⟶ X) (n m : ℕ) :
    cohomologyMap K n ((End.of d ^ m).asHom) = (cohomologyMap K n d) ^ m := by
  induction m with
  | zero => exact cohomologyMap_id K X n
  | succ m ih =>
    rw [pow_succ]
    change cohomologyMap K n (d ≫ (End.of d ^ m).asHom) = _
    rw [cohomologyMap_comp, ih, pow_succ']
    rfl

lemma persistence_dual_sequence_shortExact (K : Type) [CommRing K] (X : TopPair.{0}) :
    (relativeDualCochainShortComplexNat K X).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun n => (relativeDualCochainShortComplexNatDegreewiseSplitting K X n).shortExact

def persistence_dual_sequence_map (K : Type) [CommRing K] (X : TopPair.{0}) (d : X ⟶ X) :
    relativeDualCochainShortComplexNat K X ⟶ relativeDualCochainShortComplexNat K X where
  τ₁ := relativeCochainComplexMap K d
  τ₂ := singularCochainComplexMap K (TopPair.Hom.fst d)
  τ₃ := singularCochainComplexMap K (TopPair.Hom.snd d)
  comm₁₂ := by
    have h := congrArg HomologicalComplex.linearDualMap
      (TopPair.Homotopy.relativeChainProjection_naturality (R := K) d)
    rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at h
    exact h
  comm₂₃ := by
    have h := congrArg HomologicalComplex.linearDualMap ((chainPairFunctor K).map d).w
    rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at h
    exact h.symm

lemma persistence_pair_primitive_lift
    (K : Type) [Field K] [CharZero K] (X : TopPair.{0}) (d : X ⟶ X)
    (m : ℕ) (hm : 0 < m) (hd : End.of (TopPair.Hom.fst d) ^ m = 1)
    (ζ : K) (hvanish : ∀ n (v : Cohomology K X.snd n),
      cohomologyMap K n (TopPair.Hom.snd d) v = ζ • v → v = 0)
    (n : ℕ) (v : Cohomology K X.fst n)
    (hv : cohomologyMap K n (TopPair.Hom.fst d) v = ζ • v) :
    ∃! u : RelativeCohomology K X n,
      relativeCohomologyMap K n d u = ζ • u ∧
      relativeCohomologyToAbsolute K X n u = v := by
  have hp := persistence_pair_order X d m hd
  have hs : End.of (TopPair.Hom.snd d) ^ m = 1 := by
    have h := congrArg (TopPair.proj₂.mapEnd X) hp
    rw [map_pow, map_one] at h
    exact h
  apply persistence_sequence_eigen_lift (relativeDualCochainShortComplexNat K X)
    (persistence_dual_sequence_shortExact K X) (persistence_dual_sequence_map K X d)
    ζ ?_ ?_ hvanish n v hv
  · intro j
    apply persistence_finite_order_semisimple _ m hm
    change (relativeCohomologyMap K j d) ^ m = 1
    rw [← persistence_relative_power, hp]
    exact relativeCohomologyMap_id K X j
  · intro j
    apply persistence_finite_order_semisimple _ m hm
    change (cohomologyMap K j (TopPair.Hom.snd d)) ^ m = 1
    rw [← persistence_absolute_power, hs]
    exact cohomologyMap_id K X.snd j

lemma persistence_pair_hom_ext {X Y : TopPair.{0}} {f g : X ⟶ Y}
    (h : TopPair.Hom.fst f = TopPair.Hom.fst g) : f = g := by
  apply MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply (TopPair.isEmbedding_map Y).injective
    exact (TopPair.Hom.w_apply f x).trans
      ((congrArg (fun t : X.fst ⟶ Y.fst => t (X.map x)) h).trans
        (TopPair.Hom.w_apply g x).symm)
  · exact h

end HodgeLean.Foundations.QuotientDuality

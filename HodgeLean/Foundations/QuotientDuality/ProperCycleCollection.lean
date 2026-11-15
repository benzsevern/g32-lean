import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs
import HodgeLean.Foundations.AlgebraicTopology.Singular.CohomologyWithSupport

/-! # Supports of collected rational cycle families -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

lemma properCycle_collected_support_subset
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ) :
    a3b4_cycleSupport X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) ⊆
      ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i) := by
  classical
  intro z hz
  change Point.underlying z ∈ ⋃ ξ ∈
    (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)).support, closure {ξ} at hz
  obtain ⟨ξ, hξ, hzξ⟩ := Set.mem_iUnion₂.mp hz
  have hs : (∑ i, q i * γ i ξ) ≠ 0 := by
    change (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) ξ ≠ 0 at hξ
    simpa only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Function.locallyFinsuppWithin.mapRange_apply] using hξ
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  refine Set.mem_iUnion₂.mpr ⟨i, left_ne_zero_of_mul hi, ?_⟩
  change Point.underlying z ∈ ⋃ η ∈ (γ i).support, closure {η}
  exact Set.mem_iUnion₂.mpr ⟨ξ, right_ne_zero_of_mul hi, hzξ⟩

lemma properCycle_weighted_union_class
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (k : ℕ) (a : ∀ i, s2e_supportedClass X (γ i) k) :
    ∃ w : CohomologyWithSupport ℚ (a3b4_an X.hom)
        (⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)) (2 * k),
      forgetSupport ℚ (a3b4_an X.hom) _ (2 * k) w =
        ∑ i, q i • s2e_classToAbsolute X (γ i) k (a i) := by
  let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
  have hT : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T := by
    intro i hi z hz
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩
  exact ⟨SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
      (fun i => a3b4_cycleSupport X.hom (γ i)) T q hT a,
    SupportedClasses.forget_weightedSum (a3b4_an X.hom) (2 * k)
      (fun i => a3b4_cycleSupport X.hom (γ i)) T q hT a⟩

lemma properCycle_prime_decomposition
    (X : Scheme.{0}) [DecidableEq X] (γ : AlgebraicCycle X ℚ)
    [Fintype {ξ : X // ξ ∈ γ.support}] :
    (∑ ξ : {ξ : X // ξ ∈ γ.support},
      (Function.locallyFinsuppWithin.single ξ.1 (γ ξ.1) : AlgebraicCycle X ℚ)) = γ := by
  classical
  ext x
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  by_cases hx : x ∈ γ.support
  · rw [Finset.sum_eq_single ⟨x, hx⟩]
    · simp
    · intro i _ hne
      have hix : i.1 ≠ x := fun h => hne (Subtype.ext h)
      simp [hix, Ne.symm hix]
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  · have hγx : γ x = 0 := not_ne_iff.mp hx
    rw [hγx]
    apply Finset.sum_eq_zero
    intro i _
    have hix : i.1 ≠ x := fun h => hx (h ▸ i.2)
    simp [hix, Ne.symm hix]

lemma properCycle_pushforward_weighted_sum
    {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f]
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X ℚ) (q : I → ℚ) :
    a1p_pushforward f (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) =
      ∑ i, (a1p_pushforward f (γ i)).mapRange (q i * ·) (mul_zero _) := by
  let F : AlgebraicCycle X ℚ →+ AlgebraicCycle Y ℚ :=
    { toFun := a1p_pushforward f
      map_zero' := a1x_pushforward_zero f
      map_add' := a1p_pushforward_add f }
  change F (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => a1p_pushforward_mul f (q i) (γ i))

/-- Enlarging a finite weighted supported class preserves each literal summand.
Source: Hatcher, Algebraic Topology, section 3.1, functoriality of relative cohomology.
HC no distance; AV milestone no distance. -/
lemma properCycle_enlarge_weightedSum
    {I : Type} [Fintype I] (X : TopCat.{0}) (n : ℕ)
    (S : I → Set X) (T U : Set X) (hTU : T ⊆ U) (q : I → ℚ)
    (hST : ∀ i, q i ≠ 0 → S i ⊆ T)
    (a : ∀ i, CohomologyWithSupport ℚ X (S i) n) :
    enlargeSupport ℚ X hTU n (SupportedClasses.weightedSum X n S T q hST a) =
      SupportedClasses.weightedSum X n S U q
        (fun i hi => (hST i hi).trans hTU) a := by
  classical
  unfold SupportedClasses.weightedSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rw [map_smul]
    congr 1
    unfold enlargeSupport
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
    rfl
  · exact map_zero _

end HodgeLean.Foundations.QuotientDuality

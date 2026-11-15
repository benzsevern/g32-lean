import HodgeLean.Adapters.SupportedCycleClassesLocal
import HodgeLean.Foundations.AlgebraicTopology.Singular.CohomologyWithSupportDefs

/-!
Rational supported classes and finite weighted cycle families.
Source: Hatcher, Algebraic Topology, §3.1; Fulton, Intersection Theory, §19.1.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open TopologicalSpace HodgeLean.Foundations.Analytic
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open scoped BigOperators
namespace HodgeLean.Adapters.SupportedCycleClasses

/-- Disjoint normalized rational cycle classes give a normalized finite weighted sum.
Source: Fulton, Intersection Theory, second edition, §19.1;
SchoenCycleC2NormalizedSumHelpers.s2e_rationalOrbitCycle_normalized_sum,
generalized from orbit components to disjoint finite cycle families.
-/
theorem normalized_sum_aux {ι : Type*} [Fintype ι] {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q] (k : ℕ)
    (γ : ι → AlgebraicCycle Z ℚ)
    (hclosed : ∀ i, IsClosed (a3b4_cycleSupport q (γ i)))
    (hdisj : ∀ i j, i ≠ j → Disjoint
      (a3b4_cycleSupport q (γ i)) (a3b4_cycleSupport q (γ j)))
    (c : ∀ i, CohomologyWithSupport ℚ (a3b4_an q)
      (a3b4_cycleSupport q (γ i)) (2 * k))
    (hc : ∀ i, a3b4_IsCycleClass q (γ i) k (c i)) (a : ι → ℚ) :
    ∃ b : CohomologyWithSupport ℚ (a3b4_an q)
        (a3b4_cycleSupport q (∑ i, (γ i).mapRange (a i * ·) (mul_zero _))) (2 * k),
      a3b4_IsCycleClass q (∑ i, (γ i).mapRange (a i * ·) (mul_zero _)) k b ∧
      forgetSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (∑ i, (γ i).mapRange (a i * ·) (mul_zero _))) (2 * k) b =
        ∑ i, a i • forgetSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (γ i)) (2 * k) (c i) := by
  classical
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  let X := a3b4_an q
  let S : ι → Set X := fun i => a3b4_cycleSupport q (γ i)
  let T : Set X := a3b4_cycleSupport q (weightedCycle γ a)
  have hT : T = ⋃ i, ⋃ (_ : a i ≠ 0), S i := weightedCycle_support q γ hdisj a
  have hST : ∀ i, a i ≠ 0 → S i ⊆ T := by
    intro i ha x hx
    rw [hT]
    exact Set.mem_iUnion₂.mpr ⟨i, ha, hx⟩
  let b := SupportedClasses.weightedSum X (2 * k) S T a hST c
  refine ⟨b, ?_, SupportedClasses.forget_weightedSum_aux X (2 * k) S T a hST c⟩
  intro r e hflat x hxe hxT he
  have hxT' : x ∈ T := hxT
  rw [hT] at hxT'
  obtain ⟨t, ha, hxt⟩ := Set.mem_iUnion₂.mp hxT'
  obtain ⟨V, hxV, hoff⟩ := disjoint_family_neighbourhood S hclosed hdisj t x hxt
  have hlocal : ∀ y ∈ V, y ∈ T ↔ y ∈ S t := by
    intro y hy
    constructor
    · intro hyT
      rw [hT] at hyT
      obtain ⟨s, _, hys⟩ := Set.mem_iUnion₂.mp hyT
      by_cases hst : s = t
      · simpa only [hst] using hys
      · exact (hoff s hst y hy hys).elim
    · intro hyS
      exact hST t ha hyS
  let e' := e.restrOpen (V : Set X) V.isOpen
  have he' : a3b4_IsHolChart q e' := by
    constructor
    · intro j
      exact anrem_isHolFun_restrict (f4_analytification (Over.mk q))
        (fun _ h => h.1) (he.1 j)
    · intro j
      exact anrem_isHolFun_restrict (f4_analytification (Over.mk q))
        (fun _ h => h.1) (he.2 j)
  have hflat' : ∀ y ∈ e'.source, y ∈ S t ↔ (e' y).2 = 0 := by
    intro y hy
    exact (hlocal y hy.2).symm.trans (hflat y hy.1)
  obtain ⟨N, hNe', hNo, hxN, hnorm⟩ := hc t r e' hflat' x ⟨hxe, hxV⟩ hxt he'
  have hNV : N ⊆ (V : Set X) := fun _ hy => (hNe' hy).2
  have hNe : N ⊆ e.source := fun _ hy => (hNe' hy).1
  refine ⟨N, hNe, hNo, hxN, ?_⟩
  change relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap N T) b = _
  dsimp only [b]
  refine (weightedSum_restrict_single X (2 * k) S T a hST c t ha N
    (fun s hst y hy => hoff s hst y (hNV hy))).trans ?_
  rw [hnorm, map_smul]
  rw [localSupportMap_normalCoclass r k N (S t) T
    (fun y _ hy => hST t ha hy) e' e hflat' hflat hNe' hNe (fun _ _ => rfl)]
  rw [smul_smul]
  exact congrArg (fun z : ℚ => z • chartNormalProjectionCoclass (Fin r → ℂ) k e T hflat N hNe)
    (weightedCycle_multiplicity q γ hdisj a t x hxt V V.isOpen hxV hlocal).symm



-- A one-component coefficient-one family retains its given local normalization.
example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (k : ℕ) (γ : AlgebraicCycle Z ℚ)
    (c : CohomologyWithSupport ℚ (a3b4_an q) (a3b4_cycleSupport q γ) (2 * k))
    (hc : a3b4_IsCycleClass q γ k c) :
    ∃ b : CohomologyWithSupport ℚ (a3b4_an q)
        (a3b4_cycleSupport q (∑ _ : Unit, γ.mapRange ((1 : ℚ) * ·) (mul_zero _))) (2 * k),
      a3b4_IsCycleClass q (∑ _ : Unit, γ.mapRange ((1 : ℚ) * ·) (mul_zero _)) k b ∧
      forgetSupport ℚ (a3b4_an q) _ (2 * k) b =
        ∑ _ : Unit, (1 : ℚ) • forgetSupport ℚ (a3b4_an q) _ (2 * k) c := by
  classical
  have hγ : (∑ _ : Unit, γ.mapRange ((1 : ℚ) * ·) (mul_zero _)) = γ := by
    ext ξ
    simp
  rw [hγ]
  simp only [one_smul, Finset.univ_unique, Finset.sum_singleton]
  exact ⟨c, hc, rfl⟩

end HodgeLean.Adapters.SupportedCycleClasses

import HodgeLean.Foundations.QuotientDuality.ProperCycleCollectedComponentIsolation
import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalSupportEquality
import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedFamilyNormalization

/-! # Original local normalization of an exactly descended finite-family class -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- Exact enlargement of the independent weighted representatives retains the original complex-normal equation at every family-isolated collected-support point.
Source: Fulton, Intersection Theory, sections 1.5 and 19.1, local normalization under finite collection.
HC no distance; AV milestone no distance. -/
lemma properCycle_collected_lift_normalization_at_isolated_point
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (k : ℕ)
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (a : ∀ i, s2e_supportedClass X (γ i) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) k (a i))
    (s : s2e_supportedClass X (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) k)
    (hs : enlargeSupport ℚ (a3b4_an X.hom) (properCycle_collected_support_subset X γ q) (2 * k) s =
      SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
        (fun i => a3b4_cycleSupport X.hom (γ i))
        (⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)) q
        (fun i hi y hy => Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩) a)
    (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (heS : ∀ y ∈ e.source,
      y ∈ a3b4_cycleSupport X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) ↔ (e y).2 = 0)
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ e.source)
    (hxS : x ∈ a3b4_cycleSupport X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)))
    (ξ : X.left) (hxξ : x.underlying ∈ closure ({ξ} : Set X.left))
    (hother : ∀ i η, η ∈ (γ i).support → η ≠ ξ → x.underlying ∉ closure ({η} : Set X.left)) :
    ∃ (W : Opens (ComplexPoint X)) (hWe : (W : Set (ComplexPoint X)) ⊆ e.source), x ∈ W ∧
      relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X))
        (a3b4_cycleSupport X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)))) s =
      a3b4_multiplicity X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) x •
        chartNormalProjectionCoclass (Fin r → ℂ) k e
          (a3b4_cycleSupport X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _))) heS W hWe := by
  classical
  let Γ : AlgebraicCycle X.left ℚ := ∑ i, (γ i).mapRange (q i * ·) (mul_zero _)
  let S := a3b4_cycleSupport X.hom Γ
  let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
  let hST : S ⊆ T := properCycle_collected_support_subset X γ q
  let hT : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T :=
    fun i hi y hy => Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩
  obtain ⟨hΓξ, hΓother⟩ := properCycle_collected_component_isolation X γ q ξ x hxS hother
  obtain ⟨O, hOe, hxO, hOS⟩ := a3b4a_classSupport_local_eq_component X.hom Γ ξ hΓξ x hΓother
    (⟨e.source, e.open_source⟩ : Opens (ComplexPoint X)) hx
  obtain ⟨P, hPO, hxP, hP⟩ := properCycle_family_component_neighborhood X γ ξ x hother O hxO
  let e' := e.restrOpen (P : Set (ComplexPoint X)) P.isOpen
  have he' : a3b4_IsHolChart X.hom e' :=
    a3b4g_isHolChart_restrOpen e he (P : Set (ComplexPoint X)) P.isOpen
  have hprime : ∀ y ∈ e'.source,
      y.underlying ∈ closure ({ξ} : Set X.left) ↔ (e' y).2 = 0 := by
    intro y hy
    exact (hOS y (hPO hy.2)).symm.trans (heS y hy.1)
  have hTP (y : ComplexPoint X) (hy : y ∈ P) :
      y ∈ T ↔ y.underlying ∈ closure ({ξ} : Set X.left) := by
    constructor
    · intro hyT
      obtain ⟨i, _, hyi⟩ := Set.mem_iUnion₂.mp hyT
      exact ((hP i y hy).mp hyi).2
    · intro hyξ
      obtain ⟨i, hi, hξi⟩ := properCycle_collected_component_occurs γ q ξ hΓξ
      exact hT i hi ((hP i y hy).mpr ⟨hξi, hyξ⟩)
  have heT : ∀ y ∈ e'.source, y ∈ T ↔ (e' y).2 = 0 :=
    fun y hy => (hTP y hy.2).trans (hprime y hy)
  obtain ⟨W, hWe', hxW, hW⟩ := properCycle_weighted_isolated_component_chart_normalization
    X k γ a ha q T hT r e' heT he' x ⟨hx, hxP⟩ ξ hxξ hprime hother
  have hWe : (W : Set (ComplexPoint X)) ⊆ e.source := fun y hy => (hWe' hy).1
  have hTS : ∀ y ∈ W, y ∈ T → y ∈ S := fun y hy hyT =>
    (hOS y (hPO (hWe' hy).2)).mpr ((hTP y (hWe' hy).2).mp hyT)
  have hm : (∑ i, q i * γ i ξ) = a3b4_multiplicity X.hom Γ x := by
    rw [a3b4a_classMultiplicity_eq_component X.hom Γ ξ hΓξ x hxξ hΓother]
    simp only [Γ, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Function.locallyFinsuppWithin.mapRange_apply]
  refine ⟨W, hWe, hxW, ?_⟩
  apply properCycle_local_support_map_injective (W : Set (ComplexPoint X)) S T (2 * k)
    (fun y _ hy => hST hy) hTS
  rw [map_smul, SupportedCycleClasses.localSupportMap_normalCoclass r k
    (W : Set (ComplexPoint X)) S T (fun y _ hy => hST hy) e e' heS heT hWe hWe'
    (fun _ _ => rfl)]
  have hs' : enlargeSupport ℚ (TopCat.of (ComplexPoint X)) hST (2 * k) s =
      SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
        (fun i => a3b4_cycleSupport X.hom (γ i)) T q hT a := hs
  rw [← SupportedCycleClasses.enlargeSupport_restrict (W : Set (ComplexPoint X)) S T hST (2 * k) s,
    hs', hW, hm]

end HodgeLean.Foundations.QuotientDuality

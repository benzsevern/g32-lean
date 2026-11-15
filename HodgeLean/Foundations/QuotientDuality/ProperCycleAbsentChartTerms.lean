import HodgeLean.Foundations.QuotientDuality.ProperCycleCollection
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalization
import HodgeLean.Adapters.SupportedCycleClassesLocal

/-! # Actual finite weighted normalization with absent source terms -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A common component chart retains the exact weighted normal coclass after every absent source term is removed by its literal zero restriction.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1, rational cycle multiplicities and local normalization.
HC no distance; AV milestone no distance. -/
lemma properCycle_weighted_chart_normalization_with_absent_terms
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (k : ℕ)
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ)
    (a : ∀ i, s2e_supportedClass X (γ i) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) k (a i))
    (q : I → ℚ) (T : Set (ComplexPoint X))
    (hST : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T)
    (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (hT : ∀ y ∈ e.source, y ∈ T ↔ (e y).2 = 0)
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ e.source)
    (m : I → ℚ)
    (hpresent : ∀ i, q i ≠ 0 → x ∈ a3b4_cycleSupport X.hom (γ i) →
      (∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom (γ i) ↔ (e y).2 = 0) ∧
        m i = a3b4_multiplicity X.hom (γ i) x)
    (hmissing : ∀ i, q i ≠ 0 → x ∉ a3b4_cycleSupport X.hom (γ i) →
      (∀ y ∈ e.source, y ∉ a3b4_cycleSupport X.hom (γ i)) ∧ m i = 0) :
    ∃ (W : Opens (ComplexPoint X)) (hWe : (W : Set (ComplexPoint X)) ⊆ e.source), x ∈ W ∧
      relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) T)
        (SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
          (fun i => a3b4_cycleSupport X.hom (γ i)) T q hST a) =
      (∑ i, q i * m i) •
        chartNormalProjectionCoclass (Fin r → ℂ) k e T hT W hWe := by
  classical
  have hnorm (i : {i : I // q i ≠ 0 ∧ x ∈ a3b4_cycleSupport X.hom (γ i)}) :=
    ha i.val r e (hpresent i.val i.property.1 i.property.2).1 x hx i.property.2 he
  choose V hVe hVo hxV hVnorm using hnorm
  let Wset : Set (ComplexPoint X) := e.source ∩ ⋂ i, V i
  have hWo : IsOpen Wset := e.open_source.inter (isOpen_iInter_of_finite hVo)
  let W : Opens (ComplexPoint X) := ⟨Wset, hWo⟩
  have hWe : (W : Set (ComplexPoint X)) ⊆ e.source := Set.inter_subset_left
  have hxW : x ∈ W := ⟨hx, Set.mem_iInter.mpr hxV⟩
  refine ⟨W, hWe, hxW, ?_⟩
  unfold SupportedClasses.weightedSum
  rw [map_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hq : q i ≠ 0
  · simp only [dite_eq_left hq, map_smul]
    by_cases hxi : x ∈ a3b4_cycleSupport X.hom (γ i)
    · have hWV : (W : Set (ComplexPoint X)) ⊆ V ⟨i, hq, hxi⟩ :=
        fun y hy => Set.mem_iInter.mp hy.2 ⟨i, hq, hxi⟩
      have hlocal := a3b4a_classLocal_normalization_mono e (a3b4_cycleSupport X.hom (γ i))
        (hpresent i hq hxi).1 hWV (hVe ⟨i, hq, hxi⟩) (a i) _ (hVnorm ⟨i, hq, hxi⟩)
      let L := relativeCohomologyMap ℚ (2 * k) (SupportedCycleClasses.localSupportMap
        (W : Set (ComplexPoint X)) (a3b4_cycleSupport X.hom (γ i)) T (fun y _ hy => hST i hq hy))
      let cS := chartNormalProjectionCoclass (Fin r → ℂ) k e (a3b4_cycleSupport X.hom (γ i))
        (hpresent i hq hxi).1 (W : Set (ComplexPoint X)) (hWV.trans (hVe ⟨i, hq, hxi⟩))
      let cT := chartNormalProjectionCoclass (Fin r → ℂ) k e T hT (W : Set (ComplexPoint X)) hWe
      have hcoc : L cS = cT := SupportedCycleClasses.localSupportMap_normalCoclass (M := ComplexPoint X)
        r k (W : Set (ComplexPoint X)) (a3b4_cycleSupport X.hom (γ i)) T
        (fun y _ hy => hST i hq hy) e e (hpresent i hq hxi).1 hT (hWV.trans (hVe ⟨i, hq, hxi⟩)) hWe (fun _ _ => rfl)
      have hnr : relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) T)
          (enlargeSupport ℚ (a3b4_an X.hom) (hST i hq) (2 * k) (a i)) =
          a3b4_multiplicity X.hom (γ i) x • cT := by
        calc
          _ = L (relativeCohomologyMap ℚ (2 * k)
              (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) (a3b4_cycleSupport X.hom (γ i))) (a i)) :=
            SupportedCycleClasses.enlargeSupport_restrict (M := ComplexPoint X) (W : Set (ComplexPoint X)) (a3b4_cycleSupport X.hom (γ i)) T (hST i hq) (2 * k) (a i)
          _ = L (a3b4_multiplicity X.hom (γ i) x • cS) := congrArg L hlocal
          _ = a3b4_multiplicity X.hom (γ i) x • L cS := map_smul L _ _
          _ = a3b4_multiplicity X.hom (γ i) x • cT := congrArg (fun z => a3b4_multiplicity X.hom (γ i) x • z) hcoc
      simpa only [(hpresent i hq hxi).2] using
        (congrArg (fun z => q i • z) hnr).trans (smul_smul _ _ _)
    · have hmiss := hmissing i hq hxi
      have hz : relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) T)
          (enlargeSupport ℚ (a3b4_an X.hom) (hST i hq) (2 * k) (a i)) = 0 :=
        SupportedCycleClasses.enlargeSupport_restrict_zero (M := ComplexPoint X) W
          (a3b4_cycleSupport X.hom (γ i)) T (hST i hq) (2 * k)
          (fun y hy => hmiss.1 y (hWe hy)) (a i)
      exact (congrArg (fun z => q i • z) hz).trans (by rw [hmiss.2, mul_zero, zero_smul, smul_zero])
  · have hq0 : q i = 0 := not_ne_iff.mp hq
    simp [hq0]

end HodgeLean.Foundations.QuotientDuality

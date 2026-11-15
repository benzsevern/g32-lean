import HodgeLean.Adapters.KleimanProductChartClass

/-! # The intersection chart bridge off the singular locus of the component

Purity along the singular filtration of an intersection component and lowest-degree germ
detection reduce the weighted chart identity for the component to the same identity on some
neighborhood of each smooth support point inside the chart.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs AlgebraicTopology.Singular
open scoped ContDiff Manifold

namespace HodgeLean.Adapters

/-- A degree-`2 * (p + q)` identity between a rational multiple of the restricted class of a
codimension-`p + q` point and a class on a chart, known on a neighborhood of every smooth support
point of the chart, holds on the whole chart.
Source: SGA 1, Exposé XII, 3.1; Bott--Tu, *Differential Forms in Algebraic Topology*, §6. -/
theorem hc9k_weighted_chart_eq_of_local
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) (z : X.left) (hz : Order.coheight z = n) (U : Opens (ComplexPoint X)) (c : ℚ)
    (β : RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set (ComplexPoint X))
      (cycleComponentAnalyticClosedSupport X z : Set (ComplexPoint X))) (2 * n))
    (hloc : ∀ a ∈ U, a ∈ cycleComponentAnalyticClosedSupport X z →
      a ∉ cycleComponentSingularAnalyticClosedFiltration X z 0 →
      ∃ (W : Opens (ComplexPoint X)) (_ : a ∈ W) (hWU : W ≤ U),
        c • relativeCohomologyMap ℚ (2 * n)
            (neighborhoodSupportInclusionPairMap
              (show (W : Set (ComplexPoint X)) ⊆ (⊤ : Opens (ComplexPoint X)) from le_top)
              (cycleComponentAnalyticClosedSupport X z : Set (ComplexPoint X)))
            (supportedSingularClass X (cycleComponentAnalyticClosedSupport X z) (2 * n)
              (cycleComponentSupportedInjectiveClass X z hz)) =
          relativeCohomologyMap ℚ (2 * n)
            (neighborhoodSupportInclusionPairMap (show (W : Set (ComplexPoint X)) ⊆ U from hWU)
              (cycleComponentAnalyticClosedSupport X z : Set (ComplexPoint X))) β) :
    c • relativeCohomologyMap ℚ (2 * n)
        (neighborhoodSupportInclusionPairMap
          (show (U : Set (ComplexPoint X)) ⊆ (⊤ : Opens (ComplexPoint X)) from le_top)
          (cycleComponentAnalyticClosedSupport X z : Set (ComplexPoint X)))
        (supportedSingularClass X (cycleComponentAnalyticClosedSupport X z) (2 * n)
          (cycleComponentSupportedInjectiveClass X z hz)) = β := by
  let S := cycleComponentAnalyticClosedSupport X z
  let B := cycleComponentSingularAnalyticClosedFiltration X z 0
  let U' : Opens (ComplexPoint X) := B.compl ⊓ U
  have hU'U : (U' : Set (ComplexPoint X)) ⊆ U := fun _ h => h.2
  apply hc9k_restrict_injective_of_relH X S B (hc9k_singularFiltration_zero_le_support X z) U
    (2 * n) (hc9k_singularFiltration_relH_subsingleton X z n hz (2 * n) (by omega) 0
      (Nat.zero_le _) U)
  apply hc9k_germs_injective_offSingular X z n hz U' inf_le_left
  funext ⟨a, haU'⟩
  dsimp only
  by_cases haS : a ∈ S
  · obtain ⟨W, haW, hWU, hW⟩ := hloc a haU'.2 haS haU'.1
    let N : Opens (ComplexPoint X) := W ⊓ U'
    have hNU' : N ≤ U' := inf_le_right
    have hNW : (N : Set (ComplexPoint X)) ⊆ W := fun _ h => h.1
    refine supportRelativeCohomologyGerm_eq_of_restrict_eq (TopCat.of (ComplexPoint X))
      (S : Set (ComplexPoint X)) (2 * n) (W := N) hNU' hNU' a ⟨haW, haU'⟩ _ _ ?_
    have h := congrArg (relativeCohomologyMap ℚ (2 * n)
      (neighborhoodSupportInclusionPairMap hNW (S : Set (ComplexPoint X)))) hW
    rw [map_smul, hc9k_restrict_restrict, hc9k_restrict_restrict] at h
    have hNU's : (N : Set (ComplexPoint X)) ⊆ U' := hNU'
    change relativeCohomologyMap ℚ (2 * n) (neighborhoodSupportInclusionPairMap hNU's _) _ =
      relativeCohomologyMap ℚ (2 * n) (neighborhoodSupportInclusionPairMap hNU's _) _
    rw [hc9k_restrict_restrict, hc9k_restrict_restrict, map_smul, hc9k_restrict_restrict]
    exact h
  · rw [supportRelativeCohomologyGerm_eq_zero_of_not_mem _ _ _ S.isClosed _ _ _ haS,
      supportRelativeCohomologyGerm_eq_zero_of_not_mem _ _ _ S.isClosed _ _ _ haS]

/-- Two holomorphic maps side by side form a holomorphic map. -/
theorem hc9k_appendCoordinates_contMDiff {d : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℂ) M] {p q : ℕ} (f : C(M, Fin p → ℂ)) (h : C(M, Fin q → ℂ))
    (hf : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ω f)
    (hh : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω h) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin (p + q) → ℂ) ω (hc9k_appendCoordinates f h) := by
  refine contMDiff_pi_space.mpr fun i => Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change ContMDiff _ _ ω fun u => Fin.append (f u) (h u) (Fin.castAdd q j)
    simp only [Fin.append_left]
    exact contMDiff_pi_space.mp hf j
  · change ContMDiff _ _ ω fun u => Fin.append (f u) (h u) (Fin.natAdd p j)
    simp only [Fin.append_right]
    exact contMDiff_pi_space.mp hh j

-- Needs definitional unfolding across the relative-cup and supported-class wrappers.
set_option backward.isDefEq.respectTransparency false in
/-- At a smooth support point of a codimension-`n` point where a holomorphic normal map is a
submersion, the restricted prime class equals the pulled-back normalized class near that point.
Source: SGA 1, Exposé XII, 3.1; Bott--Tu, *Differential Forms in Algebraic Topology*, §6. -/
theorem hc9k_chart_local_of_submersion
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (n : ℕ) (z : X.left) (hz : Order.coheight z = n)
    (U : Opens (ComplexPoint X)) (g : C(U, Fin n → ℂ))
    (hzero : ∀ u : U, g u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X z)
    (hhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin n → ℂ) ω g)
    (a : ComplexPoint X) (haU : a ∈ U) (haS : a ∈ cycleComponentAnalyticClosedSupport X z)
    (haB : a ∉ cycleComponentSingularAnalyticClosedFiltration X z 0)
    (hsub : Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin n → ℂ) g ⟨a, haU⟩)) :
    ∃ (W : Opens (ComplexPoint X)) (_ : a ∈ W) (hWU : W ≤ U),
      relativeCohomologyMap ℚ (2 * n)
          (neighborhoodSupportInclusionPairMap
            (show (W : Set (ComplexPoint X)) ⊆ (⊤ : Opens (ComplexPoint X)) from le_top)
            (cycleComponentAnalyticClosedSupport X z : Set (ComplexPoint X)))
          (supportedSingularClass X (cycleComponentAnalyticClosedSupport X z) (2 * n)
            (cycleComponentSupportedInjectiveClass X z hz)) =
        relativeCohomologyMap ℚ (2 * n)
          (neighborhoodSupportInclusionPairMap (show (W : Set (ComplexPoint X)) ⊆ U from hWU)
            (cycleComponentAnalyticClosedSupport X z : Set (ComplexPoint X)))
          (relativeCohomologyMap ℚ (2 * n)
            (hc9k_normalCoordinatePair U (cycleComponentAnalyticClosedSupport X z) n g
              (fun u => (hzero u).mp))
            (normalizedPointCoclass n)) := by
  obtain rfl : dim X.left = d := SmoothOfRelativeDimension.dim_eq X.hom d
  let S := cycleComponentAnalyticClosedSupport X z
  obtain ⟨e, he, hae, heA, heI, W, haW, hWe, hW⟩ :=
    hc9k_cc_componentClass_restrict_normalChart X n z hz a haB haS
  let O : Opens (ComplexPoint X) := U ⊓ W
  let e' := e.restrOpen (O : Set (ComplexPoint X)) O.isOpen
  have he' : ∀ y ∈ e'.source, y ∈ cycleComponentSupport X z ↔ (e' y).2 = 0 :=
    fun y hy => he y hy.1
  have hsO : e'.source ⊆ O := fun _ hy => hy.2
  have hsU : e'.source ⊆ U := fun _ hy => (hsO hy).1
  have hae' : a ∈ e'.source := ⟨hae, haU, haW⟩
  have ha0 : (e' a).2 = 0 := (he a hae).mp haS
  obtain ⟨L, hL, hd⟩ := hc9k_sliceNormalMap_hasFDerivAt U S g hzero hhol e' he' a haU hae'
    ha0 heA heI hsub
  have hpull := hc9k_normalMap_pullback_eq_chartCoclass n U S g hzero e' he' hsU a hae' ha0
    L hL hd
  let N := flattenedSupportNeighborhood (Fin (dim X.left - n) → ℂ) n e' a hae'
  have hNs : (N : Set (ComplexPoint X)) ⊆ e'.source :=
    flattenedSupportNeighborhood_subset_source _ n e' a hae'
  have hNU : N ≤ U := fun _ h => (hsO (hNs h)).1
  have hNW : (N : Set (ComplexPoint X)) ⊆ W := fun _ h => (hsO (hNs h)).2
  refine ⟨N, mem_flattenedSupportNeighborhood _ n e' a hae', hNU, ?_⟩
  have hL1 := congrArg (relativeCohomologyMap ℚ (2 * n)
    (neighborhoodSupportInclusionPairMap hNW (cycleComponentSupport X z))) hW
  rw [hc9k_restrict_restrict, chartNormalProjectionCoclass_restrict] at hL1
  exact hL1.trans hpull.symm

end HodgeLean.Adapters

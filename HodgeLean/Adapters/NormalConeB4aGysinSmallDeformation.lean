import HodgeLean.Adapters.NormalConeB4aGysinSupportTrapping
import HodgeLean.Adapters.NormalConeB4aGysinTransverseCompact
import HodgeLean.Adapters.NormalConeB4aGysinTransverseDeformation

/-! # Evaluation under small transverse deformations

Continuity constructs the trapping region and the straight parameter homotopy.
Local transversality constructs the finite endpoint support.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular

/-- Small transverse members of a continuous family evaluate the initial isolated
disk by the sum of their exact ambient cycle multiplicities. -/
theorem a3b4a_gysin_small_transverse_deformation_evaluation
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (F : C(P × (Fin c → ℂ), ComplexPoint (Over.mk q)))
    (r : ℝ) (hr : 0 < r)
    (hf : ∀ x ∈ Metric.closedBall (0 : Fin c → ℂ) r,
      F (0, x) ∈ a3b4_cycleSupport q γ → x = 0)
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c))
    (hβ : a3b4_IsCycleClass q γ c β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : P, ‖a‖ < ε →
      (∀ x ∈ Metric.ball (0 : Fin c → ℂ) r, F (a, x) ∈ a3b4_cycleSupport q γ →
        ∃ C : A3b4aGysinNormalChart q γ c, F (a, x) = C.point ∧
          ∃ A : Matrix (Fin c) (Fin c) ℂ, A.det ≠ 0 ∧
            HasFDerivAt (fun v => (C.chart (F (a, v + x))).2)
              (A.mulVecLin.toContinuousLinearMap :
                (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0) →
      ∃ T : Finset (Fin c → ℂ), (T : Set (Fin c → ℂ)) ⊆ Metric.ball 0 r ∧
        (∀ x ∈ Metric.ball (0 : Fin c → ℂ) r,
          F (a, x) ∈ a3b4_cycleSupport q γ ↔ x ∈ T) ∧
        ∀ z : RelativeHomology ℚ
          (neighborhoodPointComplementPair (Metric.ball (0 : Fin c → ℂ) r) 0) (2 * c),
          relativeHomologyMap ℚ (2 * c)
            (neighborhoodPointComplementPairMap (Metric.ball (0 : Fin c → ℂ) r) 0) z =
              standardComplexLocalClass ℚ c →
          relativeCohomologyEquivDualHomology ℚ _ (2 * c)
            (relativeCohomologyMap ℚ (2 * c)
              (a3b4_supportPairMap
                (TopCat.ofHom ⟨fun u : Metric.ball (0 : Fin c → ℂ) r => F (0, u.1),
                  F.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩)
                {u : Metric.ball (0 : Fin c → ℂ) r | u.1 = 0}
                (a3b4_cycleSupport q γ)
                (fun u hu => hf u.1 (Metric.ball_subset_closedBall u.2) hu)) β) z =
            ∑ x : T, a3b4_multiplicity q γ (F (a, x.1)) := by
  classical
  let E := Fin c → ℂ
  let U := Metric.ball (0 : E) r
  let K := Metric.closedBall (0 : E) (r / 2)
  have hKU : K ⊆ U := Metric.closedBall_subset_ball (half_lt_self hr)
  obtain ⟨ε, hε, htrap⟩ := a3b4a_gysin_support_segment_trapping F
    (a3b4_cycleSupport q γ) (a3b4a_classSupport_isClosed q γ)
    (Metric.closedBall (0 : E) r) (Metric.ball (0 : E) (r / 2))
    (isCompact_closedBall _ _) Metric.isOpen_ball (by
      intro x hx hs
      rw [hf x hx hs]
      exact Metric.mem_ball_self (half_pos hr))
  refine ⟨ε, hε, ?_⟩
  intro a ha htrans
  let g : E → ComplexPoint (Over.mk q) := fun x => F (a, x)
  have hg : Continuous g := F.continuous.comp (continuous_const.prodMk continuous_id)
  have hga : ∀ x ∈ U, g x ∈ a3b4_cycleSupport q γ → x ∈ K := by
    intro x hx hs
    apply Metric.ball_subset_closedBall
    apply htrap a ha 1 x (Metric.ball_subset_closedBall hx)
    change F ((1 : ℝ) • a, x) ∈ a3b4_cycleSupport q γ
    simpa only [one_smul] using hs
  obtain ⟨T, hTK, hT⟩ := a3b4a_gysin_trapped_transverse_intersection_finset
    c (a3b4_cycleSupport q γ) (a3b4a_classSupport_isClosed q γ)
    U Metric.isOpen_ball g hg.continuousOn K (isCompact_closedBall _ _) hKU
    (by
      intro x hx hs
      obtain ⟨C, hC, A, hA, hd⟩ := htrans x (hKU hx) hs
      refine ⟨C.tangentDim, C.chart, ?_, C.support_eq, A, hA, hd⟩
      change F (a, x) ∈ C.chart.source
      rw [hC]
      exact C.mem_source)
    hga
  have hTU : (T : Set E) ⊆ U := hTK.trans hKU
  choose C hC A hA hd using fun x : T =>
    htrans x.1 (hTU x.2) ((hT x.1 (hTU x.2)).mpr x.2)
  let f₀ : C(U, ComplexPoint (Over.mk q)) :=
    ⟨fun u => F (0, u.1),
      F.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩
  let H : ContinuousMap.Homotopy f₀ ⟨fun u : U => g u.1, hg.continuousOn.domRestrict⟩ :=
    { toFun := fun tu => F ((tu.1 : ℝ) • a, tu.2.1)
      continuous_toFun := F.continuous.comp
        (((continuous_subtype_val.comp continuous_fst).smul continuous_const).prodMk
          (continuous_subtype_val.comp continuous_snd))
      map_zero_left := fun u => by
        change F ((0 : ℝ) • a, u.1) = F (0, u.1)
        rw [zero_smul]
      map_one_left := fun u => by
        change F ((1 : ℝ) • a, u.1) = F (a, u.1)
        rw [one_smul] }
  refine ⟨T, hTU, hT, ?_⟩
  intro z hz
  exact a3b4a_gysin_isolated_disk_evaluation_of_deformation U Metric.isOpen_ball
    (Metric.mem_ball_self hr) g hg.continuousOn H K (isCompact_closedBall _ _) hKU
    (Metric.mem_closedBall_self (le_of_lt (half_pos hr)))
    (fun u hu => hf u.1 (Metric.ball_subset_closedBall u.2) hu)
    (fun t u hu => Metric.ball_subset_closedBall
      (htrap a ha t u.1 (Metric.ball_subset_closedBall u.2) hu))
    T hTU hT C hC A hA hd z hz β hβ

end HodgeLean.Adapters

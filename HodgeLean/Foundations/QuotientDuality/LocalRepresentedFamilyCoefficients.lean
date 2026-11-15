import HodgeLean.Foundations.QuotientDuality.LocalSupportedCoefficients

/-! Coefficients of locally represented families along a continuous parameter space. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem locally_represented_family_coefficients
    (X : TopCat.{0}) [T2Space X] (n : ℕ) (o : LocalRationalOrientation X n)
    (S : Type) [TopologicalSpace S] (j : S → X) (hj : Continuous j)
    (μ : ∀ s : S, orientationGroup X n (j s))
    (hμ : ∀ s : S, ∃ (U : Opens X), j s ∈ U ∧
      ∃ w : RelativeHomology ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ) n,
        ∀ (t : S) (ht : j t ∈ U), relativeHomologyMap ℚ n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr ht)) w = μ t) :
    ∃ f : S → ℚ, IsLocallyConstant f ∧ ∀ s, μ s = f s • o.generator (j s) := by
  classical
  choose f hf using fun s => (o.generates (j s)).2 (μ s)
  refine ⟨f, ?_, fun s => (hf s).symm⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  obtain ⟨U, hsU, w, hw⟩ := hμ s
  obtain ⟨q, hqlc, hq⟩ := relative_open_coefficients X n o U w
  have he (t : S) (ht : j t ∈ U) : f t = q ⟨j t, ht⟩ := by
    apply (o.generates (j t)).1
    change f t • o.generator (j t) = q ⟨j t, ht⟩ • o.generator (j t)
    exact (hf t).trans ((hw t ht).symm.trans (hq ⟨j t, ht⟩))
  let k : S → U := fun t => if ht : j t ∈ U then ⟨j t, ht⟩ else ⟨j s, hsU⟩
  have hval : (fun t => (k t).val) =ᶠ[nhds s] j := by
    filter_upwards [(U.isOpen.preimage hj).mem_nhds hsU] with t ht
    change j t ∈ U at ht
    simp only [k, dif_pos ht]
  have hk : ContinuousAt k s := by
    apply IsInducing.subtypeVal.continuousAt_iff.mpr
    exact hj.continuousAt.congr hval.symm
  have hqevent : ∀ᶠ t in nhds s, q (k t) = q (k s) :=
    hk.eventually (hqlc.eventually_eq (k s))
  filter_upwards [(U.isOpen.preimage hj).mem_nhds hsU, hqevent] with t ht hqt
  change j t ∈ U at ht
  rw [he t ht, he s hsU]
  simpa only [k, dif_pos ht, dif_pos hsU] using hqt

#print axioms locally_represented_family_coefficients
end HodgeLean.Foundations.QuotientDuality

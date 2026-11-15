import HodgeLean.Foundations.QuotientDuality.LocalRepresentedFamilyCoefficients
import HodgeLean.Foundations.QuotientDuality.LocalOrientationScaling

/-! A connected local family normalizes a coherent orientation without an absolute class. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem normalize_coherent_orientation_on_connected_family
    (X : TopCat.{0}) [T2Space X] (n : ℕ) (o : LocalRationalOrientation X n)
    (S : Type) [TopologicalSpace S] [PreconnectedSpace S] [Nonempty S]
    (j : S → X) (hj : Continuous j) (μ : ∀ s : S, orientationGroup X n (j s))
    (hne : ∀ s, μ s ≠ 0)
    (hμ : ∀ s : S, ∃ (U : Opens X), j s ∈ U ∧
      ∃ w : RelativeHomology ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ) n,
        ∀ (t : S) (ht : j t ∈ U), relativeHomologyMap ℚ n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr ht)) w = μ t) :
    ∃ o' : LocalRationalOrientation X n, ∀ s, o'.generator (j s) = μ s := by
  classical
  obtain ⟨f, hflc, hf⟩ := locally_represented_family_coefficients X n o S j hj μ hμ
  let s₀ := Classical.choice (inferInstance : Nonempty S)
  let q := f s₀
  have hq : q ≠ 0 := by
    intro h
    apply hne s₀
    exact (hf s₀).trans (by rw [show f s₀ = 0 from h, zero_smul])
  refine ⟨scaledLocalOrientation X n o q hq, ?_⟩
  intro s
  change q • o.generator (j s) = μ s
  have hs : f s = q := hflc.apply_eq_of_preconnectedSpace s s₀
  exact (congrArg (fun r : ℚ => r • o.generator (j s)) hs.symm).trans (hf s).symm

#print axioms normalize_coherent_orientation_on_connected_family
end HodgeLean.Foundations.QuotientDuality

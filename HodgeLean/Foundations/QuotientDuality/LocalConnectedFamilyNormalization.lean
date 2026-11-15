import HodgeLean.Foundations.QuotientDuality.LocalRepresentedFamilyCoefficients
import HodgeLean.Foundations.QuotientDuality.LocalOrientationOfGlobal
import HodgeLean.Foundations.QuotientDuality.OrientationScaling

/-! A connected nonzero local family fixes the rational scale of a global orientation class. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem normalize_global_orientation_on_connected_family
    (X : TopCat.{0}) [T2Space X] (n : ℕ) (o : LocalRationalOrientation X n)
    (c : Homology ℚ X n) (hc : ∀ x, localOrientation X n c x = o.generator x)
    (S : Type) [TopologicalSpace S] [PreconnectedSpace S] [Nonempty S]
    (j : S → X) (hj : Continuous j) (μ : ∀ s : S, orientationGroup X n (j s))
    (hne : ∀ s, μ s ≠ 0)
    (hμ : ∀ s : S, ∃ (U : Opens X), j s ∈ U ∧
      ∃ w : RelativeHomology ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ) n,
        ∀ (t : S) (ht : j t ∈ U), relativeHomologyMap ℚ n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr ht)) w = μ t) :
    ∃ (o' : LocalRationalOrientation X n) (c' : Homology ℚ X n),
      (∀ x, localOrientation X n c' x = o'.generator x) ∧
      ∀ s, o'.generator (j s) = μ s := by
  classical
  obtain ⟨f, hflc, hf⟩ := locally_represented_family_coefficients X n o S j hj μ hμ
  let s₀ := Classical.choice (inferInstance : Nonempty S)
  let q := f s₀
  have hq : q ≠ 0 := by
    intro h
    apply hne s₀
    exact (hf s₀).trans (by rw [show f s₀ = 0 from h, zero_smul])
  have hgen : ∀ x, Function.Bijective (orientationLine X n (q • c) x) := by
    intro x
    apply orientationLine_smul_bijective X n c x q hq
    change Function.Bijective (LinearMap.toSpanSingleton ℚ _ (localOrientation X n c x))
    rw [hc x]
    exact o.generates x
  have hloc (x : X) : localOrientation X n (q • c) x = q • o.generator x := by
    change (relativeHomologyProjection ℚ (pointComplementPair x) n).hom (q • c) = _
    rw [map_smul]
    exact congrArg (q • ·) (hc x)
  refine ⟨localOrientationOfGlobal X n (q • c) hgen o.vanishes, q • c, fun _ => rfl, ?_⟩
  intro s
  change localOrientation X n (q • c) (j s) = μ s
  have hs : f s = q := hflc.apply_eq_of_preconnectedSpace s s₀
  exact (hloc (j s)).trans ((congrArg (fun r : ℚ => r • o.generator (j s)) hs.symm).trans (hf s).symm)

#print axioms normalize_global_orientation_on_connected_family
end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.QuotientDuality.LocalSmoothFundamental

/-! Detection of the actual top singular class on compact complex-charted spaces. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

theorem compact_complex_charted_top_class_ext
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] (d : ℕ)
    [ChartedSpace (Fin d → ℂ) X]
    (c c' : Homology ℚ X (2 * d))
    (hc : ∀ x, localOrientation X (2 * d) c x = localOrientation X (2 * d) c' x) :
    c = c' := by
  let A := TopPair.ofSubset (X := X) ((((⊤ : Opens X) : Set X)ᶜ) : Set X)
  letI : IsIso (relativeChainProjection ℚ A) :=
    isIso_relativeChainProjection _ ⟨fun y => y.2 trivial⟩
  letI : IsIso (relativeHomologyProjection ℚ A (2 * d)) := by
    unfold relativeHomologyProjection
    infer_instance
  have hproj : Function.Bijective (relativeHomologyProjection ℚ A (2 * d)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  apply hproj.1
  have hdim : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hdet := (j5c_compact_manifold (E := Fin d → ℂ) hdim (isCompact_univ (X := X))).2
  apply sub_eq_zero.mp
  apply hdet
  intro y hy
  rw [map_sub]
  apply sub_eq_zero.mpr
  have hn (v : Homology ℚ X (2 * d)) :
      relativeHomologyMap ℚ (2 * d)
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr (Opens.mem_top y)))
        ((relativeHomologyProjection ℚ A (2 * d)).hom v) =
        localOrientation X (2 * d) v y := by
    have h := relativeHomologyProjection_map (2 * d)
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr (Opens.mem_top y))) v
    have hi : (supportInclusionPairMap X
        (Set.singleton_subset_iff.mpr (Opens.mem_top y))).hom.right = 𝟙 X := rfl
    rw [hi] at h
    erw [homologyMap_id] at h
    exact h
  exact (hn c).trans ((hc y).trans (hn c').symm)

#print axioms compact_complex_charted_top_class_ext
end HodgeLean.Foundations.QuotientDuality

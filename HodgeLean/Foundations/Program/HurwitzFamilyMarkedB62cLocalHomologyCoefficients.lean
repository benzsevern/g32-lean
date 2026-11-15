import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cIntegralSphere
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cConvexCoefficients
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalLifting

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular

theorem b6m_standardLocalHomology_isZero_above
    (R : Type) [CommRing R] (d k : ℕ) (hk : d < k) :
    IsZero (RelativeHomology R (puncturedPair ℝ d) k) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact b6m_relativeHomology_isZero_of_absolute_and_subspace R (puncturedPair ℝ d) n
    (b6m_contractible_homology_isZero R (Fin d → ℝ) (n + 1) (by omega))
    (b6m_punctured_homology_isZero_of_dimension_le R d n (by omega))

theorem b6m_pointLocalHomology_isZero_above
    (R : Type) [CommRing R] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (x : E) {k : ℕ} (hk : n < k) :
    IsZero (RelativeHomology R (TopPair.ofSubset (X := TopCat.of E) ({x}ᶜ : Set E)) k) := by
  let L : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [hn])
  let e : E ≃ₜ (Fin n → ℝ) := (Homeomorph.subRight x).trans L.toHomeomorph
  have he : ∀ y, e y ∈ ({0}ᶜ : Set (Fin n → ℝ)) ↔ y ∈ ({x}ᶜ : Set E) := by
    intro y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_iff_not]
    change L (y - x) = 0 ↔ y = x
    rw [map_eq_zero_iff L L.injective, sub_eq_zero]
  let φ := TopPair.isoOfSubset (X := TopCat.of E) (Y := TopCat.of (Fin n → ℝ))
    (A := ({x}ᶜ : Set E)) (B := ({0}ᶜ : Set (Fin n → ℝ))) e he
  exact (b6m_standardLocalHomology_isZero_above R n k hk).of_iso
    ((relativeHomologyFunctor R k).mapIso φ)

theorem b6m_convex_local_homology
    (R : Type) [CommRing R] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    {K : Set E} (hK : Convex ℝ K) (hKc : IsCompact K) :
    (∀ k, n < k → IsZero (RelativeHomology R
      (TopPair.ofSubset (X := TopCat.of E) Kᶜ) k)) ∧
    (∀ α : RelativeHomology R (TopPair.ofSubset (X := TopCat.of E) Kᶜ) n,
      (∀ (x : E) (hx : x ∈ K), relativeHomologyMap R n
        (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr hx)) α = 0) →
      α = 0) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · refine ⟨fun k _ => b6m_relativeHomology_empty_support_isZero R E k, ?_⟩
    have := ModuleCat.subsingleton_of_isZero
      (b6m_relativeHomology_empty_support_isZero R E n)
    exact fun _ _ => Subsingleton.elim _ _
  · have hb := fun k => b6m_convex_restrict_bijective R hK hKc hx k
    refine ⟨fun k hk => ?_, fun α hα => ?_⟩
    · have := ModuleCat.subsingleton_of_isZero (b6m_pointLocalHomology_isZero_above R hn x hk)
      have := (hb k).1.subsingleton
      exact ModuleCat.isZero_of_subsingleton _
    · exact (hb n).1 (by rw [hα x hx, map_zero])

end HodgeLean.Foundations.Program

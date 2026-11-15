import HodgeLean.RealDefs.ComplexFundamentalClassDefs
import HodgeLean.RealDefs.ComplexFundamentalClassParts.C_ConvexRestrict
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.EuclideanVanishing

/-! # Vanishing and point detection along a compact convex set

`H_i(M, M; ℚ) = 0`, and for a finite-dimensional real normed space `E` of dimension `n`,
`H_i(E, E \ x; ℚ) = 0` for `i ≠ n` (upstream's computation on `Fin n → ℝ`, moved to `E` by a
linear homeomorphism). With the restriction bijection of `C_ConvexRestrict` these give
vanishing above `n` and point detection along a compact convex set (Hatcher, *Algebraic
Topology*, Lemma 3.27, step (1)).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

/-- `H_i(M, M; ℚ) = 0`: the relative chains of `(M, M)` are the cokernel of an isomorphism. -/
theorem C_relativeHomology_compl_empty_isZero (M : Type) [TopologicalSpace M] (i : ℕ) :
    IsZero (RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (∅ : Set M)ᶜ) i) := by
  let P := TopPair.ofSubset (X := TopCat.of M) (∅ : Set M)ᶜ
  have hiso : IsIso P.map := by
    refine ⟨TopCat.ofHom ⟨fun y => ⟨y, Set.notMem_empty y⟩, by fun_prop⟩, ?_, ?_⟩
    · ext y; rfl
    · ext y; rfl
  have hf : IsIso (relativeChainShortComplex ℚ P).f := by
    change IsIso (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map P.map)
    infer_instance
  have hz := ((relativeChainShortComplex_shortExact ℚ P).isIso_f_iff).mp hf
  exact (HomologicalComplex.homologyFunctor _ _ i).map_isZero hz

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- `H_k(E, E \ x; ℚ) = 0` for `k ≠ dim E`. -/
theorem C_pointLocalHomology_isZero {n : ℕ} (hn : Module.finrank ℝ E = n) (x : E) {k : ℕ}
    (hk : k ≠ n) : IsZero (RelativeHomology ℚ (pointComplementPair x) k) := by
  let L : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [hn])
  let e : E ≃ₜ (Fin n → ℝ) := (Homeomorph.subRight x).trans L.toHomeomorph
  have he : ∀ y, e y ∈ ({0}ᶜ : Set (Fin n → ℝ)) ↔ y ∈ ({x}ᶜ : Set E) := by
    intro y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_iff_not]
    change L (y - x) = 0 ↔ y = x
    rw [map_eq_zero_iff L L.injective, sub_eq_zero]
  let φ := TopPair.isoOfSubset (X := TopCat.of E) (Y := TopCat.of (Fin n → ℝ))
    (A := ({x}ᶜ : Set E)) (B := ({0}ᶜ : Set (Fin n → ℝ))) e he
  exact (standardLocalHomology_isZero_of_ne n k hk).of_iso
    ((relativeHomologyFunctor ℚ k).mapIso φ)

/-- Along a compact convex `K ⊆ E`, local homology vanishes above `dim E` and is detected by
points. -/
theorem C_convex {n : ℕ} (hn : Module.finrank ℝ E = n) {K : Set E} (hK : Convex ℝ K)
    (hKc : IsCompact K) :
    LocalHomologyVanishesAbove E n K ∧ LocalHomologyDetectedByPoints E n K := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · have hs : ∀ i, Subsingleton
        (RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of E) (∅ : Set E)ᶜ) i) :=
      fun i => ModuleCat.subsingleton_of_isZero (C_relativeHomology_compl_empty_isZero E i)
    exact ⟨fun i _ => hs i, fun α _ => (hs n).elim _ _⟩
  · have hb := fun i => C_convex_restrict_bijective hK hKc hx i
    refine ⟨fun i hi => ?_, fun α hα => ?_⟩
    · have := ModuleCat.subsingleton_of_isZero (C_pointLocalHomology_isZero hn x (k := i) (by omega))
      exact (hb i).1.subsingleton
    · exact (hb n).1 (by rw [hα x hx, map_zero])

end HodgeLean.RealDefs

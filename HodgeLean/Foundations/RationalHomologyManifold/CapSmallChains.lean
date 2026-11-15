import HodgeLean.Foundations.RationalHomologyManifold.CapSupport

/-! The actual relative cap operation on subordinate singular chains.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A cochain zero on the first member of a two-set cover caps subordinate chains into the second relative subspace.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; the subordinate-chain relative cap construction.
HC no distance; AV milestone no distance.
-/
theorem relative_cap_coverSmall_zero (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) U).map) p φ = 0)
    (w : (CoverSmallCoefficientSingularChainComplex ℚ X ![U, A]).X (p + q)) :
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f q
      (cap ℚ p q φ ((coverSmallCoefficientSingularChainInclusion ℚ X ![U, A]).f (p + q) w)) = 0 := by
  let S := (coverSmallSingularSubcomplex X ![U, A] : SSet)
  let inc := (coverSmallSingularSubcomplex X ![U, A]).ι
  let P := TopPair.ofSubset (X := X) A
  let f := (coverSmallCoefficientSingularChainInclusion ℚ X ![U, A]).f (p + q) ≫
    capHom ℚ p q φ ≫ (relativeChainProjection ℚ P).f q
  have hf : f = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    let s := inc.app (Opposite.op (SimplexCategory.mk (p + q))) σ
    have hsmall : Set.range (X.toSSetObjEquiv _ s) ⊆ U ∨
        Set.range (X.toSSetObjEquiv _ s) ⊆ A := by
      have hmem : s ∈ (coverSmallSingularSubcomplex X ![U, A]).obj _ := σ.property
      obtain ⟨i, v, hv⟩ := (mem_coverSmallSingularSubcomplex_iff_exists_preimage X ![U, A] s).mp hmem
      have hi := (singularSimplex_subspace_image_iff X (![U, A] i) (p + q) s).mp ⟨v, hv⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hinc := ConcreteCategory.congr_hom
      (SSet.ι_chainComplexMap_f (X := S) (Y := TopCat.toSSet.obj X) (f := inc)
        (R := ModuleCat.of ℚ ℚ) σ) a
    change (coverSmallCoefficientSingularChainInclusion ℚ X ![U, A]).f (p + q)
        ((S.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a) =
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) s).hom a) at hinc
    have hiota : (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) s).hom a) =
        a • chainOfSimplex ℚ s := by
      rw [chainOfSimplex, ← map_smul]
      simp only [smul_eq_mul, mul_one]
    change (relativeChainProjection ℚ P).f q
      (cap ℚ p q φ ((coverSmallCoefficientSingularChainInclusion ℚ X ![U, A]).f (p + q)
        ((S.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a))) = 0
    rw [hinc, hiota, map_smul, map_smul,
      relative_cap_supported_simplex_zero X U A p q φ hφ s hsmall, smul_zero]
  exact ConcreteCategory.congr_hom hf w

#print axioms relative_cap_coverSmall_zero
/-- A locally zero cochain caps every sufficiently subdivided finite chain to zero near a specified support set.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; subordinate subdivision and the relative cap formula.
HC no distance; AV milestone no distance.
-/
theorem relative_cap_subdivision_eventually_zero (X : TopCat.{0}) (U A : Set X)
    (hU : IsOpen U) (hA : IsOpen A) (hcover : U ∪ A = Set.univ) (p q : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) U).map) p φ = 0)
    (z : (SingularChainComplex ℚ X).X (p + q)) :
    ∃ m : ℕ, ∀ r : ℕ,
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f q
        (cap ℚ p q φ ((rationalSubdivisionIterate X (m + r)).f (p + q) z)) = 0 := by
  obtain ⟨m, w, hw⟩ := rationalSubdivision_eventually_small X ![U, A]
    (by intro i; fin_cases i <;> assumption)
    (by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      have hx : x ∈ U ∪ A := by rw [hcover]; trivial
      rcases hx with hx | hx
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩) (p + q) z
  refine ⟨m, fun r => ?_⟩
  obtain ⟨v, hv⟩ := rationalSubdivision_small_add X ![U, A] (p + q) m r z w hw
  rw [← hv]
  exact relative_cap_coverSmall_zero X U A p q φ hφ v

#print axioms relative_cap_subdivision_eventually_zero
end HodgeLean.Foundations.RationalHomologyManifold

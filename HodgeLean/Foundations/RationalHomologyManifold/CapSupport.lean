import HodgeLean.Foundations.RationalHomologyManifold.SmallChainSupport
import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCap

/-! Local support estimates for the actual Alexander–Whitney cap construction.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A face or degeneracy of a singular simplex retains its geometric support.
Source: Hatcher, Algebraic Topology, section 2.1; functoriality of singular simplices and subspace inclusions.
HC no distance; AV milestone no distance.
-/
theorem singularSimplex_map_support (X : TopCat.{0}) (A : Set X) (m n : ℕ)
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (hs : Set.range (X.toSSetObjEquiv _ s) ⊆ A) :
    Set.range (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).map f.op s)) ⊆ A := by
  obtain ⟨t, ht⟩ := singularSimplex_lift_subspace X A n s hs
  apply (singularSimplex_subspace_image_iff X A m _).mp
  refine ⟨(TopCat.toSSet.obj (TopCat.of A)).map f.op t, ?_⟩
  have h := ConcreteCategory.congr_hom ((TopCat.toSSet.map (TopPair.ofSubset (X := X) A).map).naturality f.op) t
  change (TopCat.toSSet.map (TopPair.ofSubset (X := X) A).map).app _
      ((TopCat.toSSet.obj (TopCat.of A)).map f.op t) =
    (TopCat.toSSet.obj X).map f.op
      ((TopCat.toSSet.map (TopPair.ofSubset (X := X) A).map).app _ t) at h
  exact h.trans (congrArg ((TopCat.toSSet.obj X).map f.op) ht)

#print axioms singularSimplex_map_support
/-- A cochain whose restriction to a subspace is zero vanishes on every simplex contained in that subspace.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.1; restriction of singular cochains.
HC no distance; AV milestone no distance.
-/
theorem cochain_zero_on_supported_simplex (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) A).map) p φ = 0)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk p)))
    (hs : Set.range (X.toSSetObjEquiv _ s) ⊆ A) :
    φ (chainOfSimplex ℚ s) = 0 := by
  obtain ⟨t, ht⟩ := singularSimplex_lift_subspace X A p s hs
  have h := LinearMap.congr_fun hφ (chainOfSimplex ℚ t)
  rw [cochainMap_apply, chainOfSimplex_map, ht] at h
  exact h

#print axioms cochain_zero_on_supported_simplex

/-- Projection of a simplex lying in the relative subspace is zero in the actual relative chain quotient.
Source: Hatcher, Algebraic Topology, section 2.1; relative singular chains.
HC no distance; AV milestone no distance.
-/
theorem relativeProjection_supported_simplex_zero (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (hs : Set.range (X.toSSetObjEquiv _ s) ⊆ A) :
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f n
      (chainOfSimplex ℚ s) = 0 := by
  obtain ⟨t, ht⟩ := singularSimplex_lift_subspace X A n s hs
  apply (relativeChainProjection_zero_iff (TopPair.ofSubset (X := X) A) n _).mpr
  refine ⟨chainOfSimplex ℚ t, ?_⟩
  change ((SSet.chainComplexMap
    (TopCat.toSSet.map (TopPair.ofSubset (X := X) A).map) (ModuleCat.of ℚ ℚ)).f n).hom
      (chainOfSimplex ℚ t) = chainOfSimplex ℚ s
  rw [chainOfSimplex_map, ht]

#print axioms relativeProjection_supported_simplex_zero

/-- Cap vanishes relatively on a simplex contained either in the zero-cochain region or in the relative subspace.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; the front/back cap formula and relative support.
HC no distance; AV milestone no distance.
-/
theorem relative_cap_supported_simplex_zero (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) U).map) p φ = 0)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (p + q))))
    (hs : Set.range (X.toSSetObjEquiv _ s) ⊆ U ∨ Set.range (X.toSSetObjEquiv _ s) ⊆ A) :
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f q
      (cap ℚ p q φ (chainOfSimplex ℚ s)) = 0 := by
  rw [cap_chainOfSimplex, map_smul]
  rcases hs with hs | hs
  · have hzero : φ (chainOfSimplex ℚ (frontFace (TopCat.toSSet.obj X) s)) = 0 :=
      cochain_zero_on_supported_simplex X U p φ hφ _
        (singularSimplex_map_support X U p (p + q) (frontInclusion p q) s hs)
    rw [hzero, zero_smul]
  · have hzero : (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f q
        (chainOfSimplex ℚ (backFace (TopCat.toSSet.obj X) s)) = 0 :=
      relativeProjection_supported_simplex_zero X A q _
        (singularSimplex_map_support X A q (p + q) (backInclusion p q) s hs)
    rw [hzero, smul_zero]

#print axioms relative_cap_supported_simplex_zero
end HodgeLean.Foundations.RationalHomologyManifold

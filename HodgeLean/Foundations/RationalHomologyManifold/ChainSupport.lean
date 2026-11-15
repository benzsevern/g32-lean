import HodgeLean.Foundations.RationalHomologyManifold.SupportedChainPatching

/-! Supported simplices and the actual relative singular-chain quotient.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Every singular simplex whose image lies in a subspace is the image of an actual subspace simplex.
Source: Hatcher, Algebraic Topology, section 2.1, relative singular chains.
HC no distance; AV milestone no distance.
-/
theorem singularSimplex_lift_subspace (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (hs : Set.range (X.toSSetObjEquiv _ s) ⊆ A) :
    ∃ t, (TopCat.toSSet.map (TopPair.ofSubset (X := X) A).map).app _ t = s := by
  let g : C(Convexity.StdSimplex ℝ (Fin (n + 1)), A) :=
    ⟨fun x => ⟨(X.toSSetObjEquiv _ s) x, hs ⟨x, rfl⟩⟩,
      (X.toSSetObjEquiv _ s).continuous.subtype_mk _⟩
  refine ⟨((TopCat.of A).toSSetObjEquiv _).symm g, ?_⟩
  apply (X.toSSetObjEquiv _).injective
  ext x
  change (((TopCat.of A).toSSetObjEquiv _
    (((TopCat.of A).toSSetObjEquiv _).symm g)) x).val = (X.toSSetObjEquiv _ s) x
  rw [Equiv.apply_symm_apply]
  rfl

#print axioms singularSimplex_lift_subspace
/-- Membership in the image of subspace simplices is equivalent to the geometric image condition.
Source: Hatcher, Algebraic Topology, section 2.1, relative singular chains.
HC no distance; AV milestone no distance.
-/
theorem singularSimplex_subspace_image_iff (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (∃ t, (TopCat.toSSet.map (TopPair.ofSubset (X := X) A).map).app _ t = s) ↔
      Set.range (X.toSSetObjEquiv _ s) ⊆ A := by
  constructor
  · rintro ⟨t, rfl⟩ x ⟨u, rfl⟩
    change (((TopCat.of A).toSSetObjEquiv _ t) u).val ∈ A
    exact (((TopCat.of A).toSSetObjEquiv _ t) u).property
  · exact singularSimplex_lift_subspace X A n s

#print axioms singularSimplex_subspace_image_iff
/-- A simplex is absent from a subspace precisely when some point of its image lies outside that subspace.
Source: Hatcher, Algebraic Topology, section 2.1, relative singular chains.
HC no distance; AV milestone no distance.
-/
theorem singularSimplex_absent_subspace_iff (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (∀ t, s ≠ (TopCat.toSSet.map (TopPair.ofSubset (X := X) A).map).app _ t) ↔
      ∃ x, (X.toSSetObjEquiv _ s) x ∉ A := by
  classical
  constructor
  · intro h
    by_contra hn
    have himage : Set.range (X.toSSetObjEquiv _ s) ⊆ A := by
      rintro _ ⟨x, rfl⟩
      by_contra hx
      exact hn ⟨x, hx⟩
    obtain ⟨t, ht⟩ := singularSimplex_lift_subspace X A n s himage
    exact h t ht.symm
  · rintro ⟨x, hx⟩ t ht
    have himage := (singularSimplex_subspace_image_iff X A n s).mp ⟨t, ht.symm⟩
    exact hx (himage ⟨x, rfl⟩)

#print axioms singularSimplex_absent_subspace_iff
end HodgeLean.Foundations.RationalHomologyManifold

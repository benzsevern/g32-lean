import HodgeLean.Foundations.RationalHomologyManifold.Defs
import HodgeLean.Foundations.RationalHomologyManifold.EuclideanNeighborhoodRetract
import HodgeLean.Foundations.RationalHomologyManifold.EuclideanOpenBound

/-! The singular homological dimension of open subsets of a finite polyhedron.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- An open subspace of a finite polyhedron has no singular homology above the ambient dimension.
Source: Hatcher, Algebraic Topology, section 2.2, cellular homology; Appendix A, polyhedra.
HC no distance; AV milestone no distance.
-/
theorem finiteTriangulation_open_homology_bound (X : TopCat.{0})
    (t : FiniteTriangulation X) (U : TopCat.{0}) (j : U ⟶ X)
    (hj : Topology.IsOpenEmbedding j) (i : ℕ) (hi : t.ambient < i) :
    Subsingleton (Homology ℚ U i) := by
  obtain ⟨W, hW, r, hr⟩ := finite_complex_euclidean_neighborhood_retract
    t.complex t.finite_faces
  let f : C(W, X) := ⟨t.realization ∘ r, t.realization.continuous.comp r.continuous⟩
  let V : TopologicalSpace.Opens W :=
    ⟨f ⁻¹' Set.range j, hj.isOpen_range.preimage f.continuous⟩
  let e : U ≃ₜ Set.range j := hj.toIsEmbedding.toHomeomorph
  let k : U → V := fun u =>
    ⟨⟨(t.realization.symm (j u)).val, hW (t.realization.symm (j u)).property⟩, by
      change f _ ∈ Set.range j
      change t.realization (r _) ∈ Set.range j
      rw [hr, t.realization.apply_symm_apply]
      exact ⟨u, rfl⟩⟩
  have hk : Continuous k :=
    (((continuous_subtype_val.comp (t.realization.symm.continuous.comp j.hom.continuous)).subtype_mk _).subtype_mk _)
  let g : V → U := fun v => e.symm ⟨f v.val, v.property⟩
  have hg : Continuous g :=
    e.symm.continuous.comp ((f.continuous.comp continuous_subtype_val).subtype_mk _)
  have hkg : (TopCat.ofHom ⟨k, hk⟩) ≫ (TopCat.ofHom ⟨g, hg⟩) = 𝟙 U := by
    ext u
    apply e.injective
    change e (e.symm _) = e u
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change t.realization (r ⟨(t.realization.symm (j u)).val,
      hW (t.realization.symm (j u)).property⟩) = j u
    rw [hr, t.realization.apply_symm_apply]
  have hV : Subsingleton (Homology ℚ (TopCat.of V) i) :=
    euclidean_open_homology_bound t.ambient (TopCat.of V)
      (TopCat.ofHom ⟨fun v => v.val.val, continuous_subtype_val.comp continuous_subtype_val⟩)
      (W.isOpen.isOpenEmbedding_subtypeVal.comp V.isOpen.isOpenEmbedding_subtypeVal) i hi
  exact (homology_injective_of_retraction _ _ hkg i).subsingleton

#print axioms finiteTriangulation_open_homology_bound

end HodgeLean.Foundations.RationalHomologyManifold

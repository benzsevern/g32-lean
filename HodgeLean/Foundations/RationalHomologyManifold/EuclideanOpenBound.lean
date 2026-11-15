import HodgeLean.Foundations.RationalHomologyManifold.ManifoldHomologyBound
import HodgeLean.Foundations.RationalHomologyManifold.RetractHomology
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! Homology bounds for open Euclidean subspaces.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Open embeddings transport the homology bound of open subsets of a compact manifold.
Source: Hatcher, Algebraic Topology, section 2.1, functoriality.
HC no distance; AV milestone no distance.
-/
theorem open_embedding_charted_bound (M : TopCat.{0}) [CompactSpace M] [T2Space M]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hn : Module.finrank ℝ E = n) [ChartedSpace E M]
    (U : TopCat.{0}) (j : U ⟶ M) (hj : Topology.IsOpenEmbedding j)
    (i : ℕ) (hi : n < i) : Subsingleton (Homology ℚ U i) := by
  let V : TopologicalSpace.Opens M := ⟨Set.range j, hj.isOpen_range⟩
  let e : U ≃ₜ V := hj.toIsEmbedding.toHomeomorph
  have hv := compact_charted_open_homology_bound M n hn V i hi
  have hinj := homology_injective_of_retraction
    (TopCat.ofHom ⟨e, e.continuous⟩) (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩)
    (by ext x; exact e.symm_apply_apply x) i
  exact hinj.subsingleton

/-- Open Euclidean subspaces have homology only up to the Euclidean dimension.
Source: Hatcher, Algebraic Topology, Lemma 3.27, via stereographic projection.
HC no distance; AV milestone no distance.
-/
theorem euclidean_open_homology_bound (n : ℕ) (U : TopCat.{0})
    (j : U ⟶ TopCat.of (EuclideanSpace ℝ (Fin n)))
    (hj : Topology.IsOpenEmbedding j) (i : ℕ) (hi : n < i) :
    Subsingleton (Homology ℚ U i) := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let v : S := ⟨EuclideanSpace.single 0 1, by rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_single]; norm_num⟩
  let e := stereographic' n v
  have he : Topology.IsOpenEmbedding e.symm :=
    e.symm.isOpenEmbedding (stereographic'_target v)
  exact open_embedding_charted_bound (TopCat.of S) n finrank_euclideanSpace_fin U
    (TopCat.ofHom ⟨e.symm ∘ j, he.continuous.comp j.hom.continuous⟩)
    (he.comp hj) i hi

#print axioms euclidean_open_homology_bound
end HodgeLean.Foundations.RationalHomologyManifold

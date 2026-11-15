import HodgeLean.Foundations.Semialgebraic.CompatibleTriangulationProofs

/-! General compact semialgebraic triangulations and pointed neighbourhoods.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Filter Topology
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation

/-- Compact compatible triangulation.
Source: Coste, An Introduction to Semialgebraic Geometry (2002), Theorem 4.4; source declaration s2v_hardt6rb_compact_compatible_triangulation. -/
theorem compact_compatible_triangulation (n : ℕ) : ∀ {m : ℕ}
    (f : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (b : Fin m → s2v_t11b_Formula n),
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ ∃ h : K.space ≃ₜ f.realize,
        (∀ j, ∃ S : Finset (Finset (EuclideanSpace ℝ (Fin n))),
          (↑S : Set _) ⊆ K.faces ∧
          f.realize ∩ (b j).realize = (fun x : K.space => (h x).val) ''
            {x : K.space | ∃ s ∈ S, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ G : s2v_t11b_Formula (n + n), ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
          (∀ i, z (Fin.castAdd n i) = x.val i) ∧
          (∀ i, z (Fin.natAdd n i) = (h x).val i) := by
  intro m f hf b
  exact compact_compatible_triangulation_aux n f hf b

example : ContractibleSpace (Set.Icc (0 : ℝ) 1) :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩

/-- Common full subdivision.
Source: Rourke and Sanderson, Introduction to Piecewise-Linear Topology (1972), Chapter 2; source declaration s2v_hardt6rb_common_full_subdivision on cloud/cyc-i2-pair2. -/
theorem common_full_subdivision {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      ∀ D : Geometry.SimplicialComplex ℝ E, D.faces ⊆ K.faces →
        ∃ M : Geometry.SimplicialComplex ℝ E, M.faces.Finite ∧ M.faces ⊆ L.faces ∧
          M.space = D.space ∧
          (∀ s ∈ L.faces, (∀ x ∈ s, x ∈ M.vertices) → s ∈ M.faces) := by
  exact common_full_subdivision_aux K hK

example : ContractibleSpace (Set.Icc (0 : ℝ) 1) :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩

/-- Compact full pair triangulation.
Source: Coste (2002), Theorem 4.4; Rourke and Sanderson (1972), Chapter 2; source declaration s2e_pair_boolean_full_triangulation on cloud/cyc-i2-pair2. -/
theorem compact_full_pair_triangulation {n : ℕ}
    (f b : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (hb : IsClosed (Subtype.val ⁻¹' b.realize : Set f.realize)) :
    ∃ L M : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      L.faces.Finite ∧ M.faces.Finite ∧ M.faces ⊆ L.faces ∧
      (∀ s ∈ L.faces, (∀ x ∈ s, x ∈ M.vertices) → s ∈ M.faces) ∧
      ∃ h : L.space ≃ₜ f.realize,
        ∀ x : L.space, (h x).val ∈ b.realize ↔ x.val ∈ M.space := by
  exact compact_full_pair_triangulation_aux f b hf hb

example : ContractibleSpace (Set.Icc (0 : ℝ) 1) :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩

/-- Polyhedron open basis.
Source: Bredon, Sheaf Theory, 2nd ed., III.1; source declaration s4_q2a1_open_basis. -/
theorem polyhedron_open_basis (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (x : K.space) (U : Set K.space) (hU : U ∈ nhds x) :
    ∃ V : Set K.space, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ContractibleSpace V := by
  exact polyhedron_open_basis_aux n K hK x U hU

example : ContractibleSpace (Set.Icc (0 : ℝ) 1) :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩

/-- Compact pair neighbourhood deformation.
Source: Rourke and Sanderson (1972), Chapter 3, regular neighbourhoods; source declaration s2e_pair_boolean_neighbourhood_deformation on cloud/cyc-i2-pair2. -/
theorem compact_pair_neighbourhood_deformation {n : ℕ}
    (f b : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (hb : IsClosed (Subtype.val ⁻¹' b.realize : Set f.realize)) :
    let Q := TopPair.ofSubset (X := TopCat.of f.realize) (Subtype.val ⁻¹' b.realize)
    ∃ (U : TopCat.{0}) (j : Q.snd ⟶ U) (k : U ⟶ Q.fst),
      j ≫ k = Q.map ∧ Topology.IsOpenEmbedding k ∧
      ∃ q : U ⟶ Q.snd, j ≫ q = 𝟙 Q.snd ∧
        ∃ H : TopCat.Homotopy (𝟙 U) (q ≫ j),
          ∀ (t : unitInterval) (a : Q.snd), H (t, j a) = j a := by
  exact compact_pair_neighbourhood_deformation_aux f b hf hb

example : ContractibleSpace (Set.Icc (0 : ℝ) 1) :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩

end Semialgebraic.CompatibleTriangulation

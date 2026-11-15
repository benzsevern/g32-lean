import HodgeLean.Foundations.QuotientDuality.ProperCycleCofinalMarkedModel
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Marked

/-! # Actual common finite neighborhood models for algebraic closed marks -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology TopologicalSpace
open HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

/-- Every finite family of actual algebraic closed immersions has cofinal common finite subcomplex models, without ambient smoothness.
Source: Hartshorne, Algebraic Geometry, II.3 and II.5;
Bochnak, Coste and Roy, Real Algebraic Geometry, theorem 9.2.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_algebraic_closed_marks_cofinal_model
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    {r : ℕ} (Z : Fin r → Over (Spec ↧ℂ)) (i : ∀ j, Z j ⟶ X)
    [∀ j, IsClosedImmersion (i j).left]
    (x : ComplexPoint X) (P : Opens (ComplexPoint X)) (hxP : x ∈ P) :
    ∃ (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))),
      K.faces.Finite ∧ ∃ f : K.space → ComplexPoint X, IsEmbedding f ∧
        IsCompact (Set.range f) ∧ Set.range f ⊆ P ∧ Set.range f ∈ 𝓝 x ∧
          ∀ j : Fin r, ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
            L.faces.Finite ∧ L.faces ⊆ K.faces ∧
              ∀ z : K.space, f z ∈ Set.range (Point.map (i j)) ↔ z.val ∈ L.space := by
  obtain ⟨c, hxc⟩ := Marked.local_subsets X Z i x
  obtain ⟨K, hK, f, hf, hcompact, hsub, hnb, hmarks⟩ :=
    properCycle_cofinal_marked_chart_model c ⟨x, hxc⟩ P hxP
  exact ⟨c.n + c.n, K, hK, f, hf, hcompact, hsub, hnb, hmarks⟩

end HodgeLean.Foundations.QuotientDuality

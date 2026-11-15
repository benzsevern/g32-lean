import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicMarkedModel
import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedMarkCharts
import HodgeLean.Foundations.QuotientDuality.ProperCycleEmbeddedSupportTransfer

/-! # Actual cofinal support purity for dimension-bounded algebraic closed subsets -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular Topology TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- An algebraic dimension bound and actual ambient local concentration give cofinal supported vanishing without ambient smoothness.
Source: Bredon, Sheaf Theory, second edition, V.9;
Bochnak, Coste and Roy, Real Algebraic Geometry, theorem 9.2.1;
EGA IV, 17.11.1, and Noetherian induction.
HC no distance; AV milestone no distance. -/
lemma properCycle_algebraic_support_cofinal_relative_vanishes
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]
    [T1Space (ComplexPoint X)]
    (S : Closeds X.left) (d : ℕ) (hdim : topologicalKrullDim S ≤ d)
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : ComplexPoint X,
      Subsingleton (orientationGroup (TopCat.of (ComplexPoint X)) j x))
    (n : ℕ) (hbound : n + (2 * d + 1) ≤ N)
    (x : ComplexPoint X) (P : Opens (ComplexPoint X)) (hxP : x ∈ P) :
    ∃ Q : Opens (ComplexPoint X), Q ≤ P ∧ x ∈ Q ∧
      IsZero (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (Q : Set (ComplexPoint X))
          (Point.underlying ⁻¹' (S : Set X.left))) n) := by
  classical
  let l := (reducedSmoothStratification X.hom S).length
  let Z : Fin (l + 1) → Over (Spec ↧ℂ) := fun j =>
    Over.mk (reducedClosedStructureMap X.hom (reducedSmoothClosedFiltration X.hom S j.val))
  let i : ∀ j, Z j ⟶ X := fun j =>
    properCycle_reduced_closed_map X (reducedSmoothClosedFiltration X.hom S j.val)
  letI (j : Fin (l + 1)) : IsClosedImmersion (i j).left := by
    dsimp [i]
    infer_instance
  obtain ⟨a, K, hK, f, hf, _, hfP, hxnb, hmarks⟩ :=
    properCycle_algebraic_closed_marks_cofinal_model X Z i x P hxP
  letI : LinearOrder (EuclideanSpace ℝ (Fin a)) := IsWellOrder.linearOrder WellOrderingRel
  have hvfinite : K.vertices.Finite :=
    Set.Finite.preimage (fun _ _ _ _ h => Finset.singleton_injective h) hK
  let V := hvfinite.toFinset
  have hV : ∀ b ∈ K.vertices, b ∈ V := fun b hb => hvfinite.mem_toFinset.mpr hb
  have hrange (j : Fin (l + 1)) : Set.range (Point.map (i j)) =
      Point.underlying ⁻¹' (reducedSmoothClosedFiltration X.hom S j.val : Set X.left) := by
    rw [range_map_of_closedImmersion]
    change {z : ComplexPoint X | z.underlying ∈ Set.range (reducedClosedSubschemeι _)} = _
    rw [range_reducedClosedSubschemeι]
    rfl
  let j0 : Fin (l + 1) := ⟨0, by omega⟩
  obtain ⟨D, _, hDK, hDmark⟩ := hmarks j0
  have hmark : ∀ z : K.space, f z ∈ Point.underlying ⁻¹' (S : Set X.left) ↔ z.val ∈ D.space := by
    intro z
    have hh := hDmark z
    rw [hrange j0] at hh
    exact hh
  let Q : Opens (ComplexPoint X) := ⟨interior (Set.range f), isOpen_interior⟩
  have hQ : (Q : Set (ComplexPoint X)) ⊆ Set.range f := interior_subset
  refine ⟨Q, hQ.trans hfP, mem_interior_iff_mem_nhds.mpr hxnb, ?_⟩
  apply properCycle_embedded_original_relative_vanishes K D hK hDK V hV
    (TopCat.of (ComplexPoint X)) f hf _ hmark Q hQ N
    (fun j hj y _ => hvan j hj y) d n hbound
  intro y hyQ hyD
  have hyS : (f y).underlying ∈ S := (hmark y).mpr hyD
  obtain ⟨k, hk, m, hm, φ, hyk, hφ⟩ := properCycle_reduced_mark_chart_cover X S d hdim (f y) hyS
  let jk : Fin (l + 1) := ⟨k, by change k < l at hk; omega⟩
  obtain ⟨L, _, hLK, hLmark⟩ := hmarks jk
  exact ⟨Set.range (Point.map (i jk)), L, hLK, hLmark, m, φ, hyk, hm, hφ⟩

end HodgeLean.Foundations.QuotientDuality

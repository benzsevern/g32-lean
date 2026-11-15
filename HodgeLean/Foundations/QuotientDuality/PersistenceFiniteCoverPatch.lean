import HodgeLean.Foundations.QuotientDuality.PersistenceMarkedChartPatch
import HodgeLean.Foundations.QuotientDuality.PersistenceFiniteTopology
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Marked

/-! Actual ambient homotopy patches for closed loci in finite projective covers. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_finite_cover_closed_locus_global_patch
    (W B E : Over (Spec ↧ℂ)) [IsProjective B.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ W) [IsClosedImmersion j.left]
    (x : ComplexPoint W) (hx : x ∈ Set.range (Point.map j)) :
    ∃ O : Set (ComplexPoint W), IsOpen O ∧ x ∈ O ∧
      ∃ (R : C(ComplexPoint W, ComplexPoint W))
        (G : ContinuousMap.Homotopy (ContinuousMap.id (ComplexPoint W)) R),
        (∀ (t : unitInterval) (a : ComplexPoint W), a ∈ Set.range (Point.map j) →
          G (t, a) = a) ∧
        ∀ y ∈ O, R y ∈ Set.range (Point.map j) := by
  letI : CompactSpace (ComplexPoint W) := persistence_finite_cover_compactSpace W B β
  letI : T2Space (ComplexPoint W) := persistence_finite_cover_t2Space W B β
  letI : LocallyOfFiniteType W.hom := by
    rw [← Over.w β]
    infer_instance
  obtain ⟨c, hxc⟩ := Marked.local_subsets W (fun _ : Fin 1 => E) (fun _ => j) x
  exact persistence_marked_chart_global_patch c (0 : Fin 1) ⟨x, hxc⟩ hx

lemma persistence_finite_cover_closed_locus_finite_patches
    (W B E : Over (Spec ↧ℂ)) [IsProjective B.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ W) [IsClosedImmersion j.left] :
    let A := Set.range (Point.map j)
    ∃ (s : Finset A) (O : s → Set (ComplexPoint W))
      (R : s → C(ComplexPoint W, ComplexPoint W))
      (G : ∀ k : s, ContinuousMap.Homotopy (ContinuousMap.id (ComplexPoint W)) (R k)),
      (∀ k, IsOpen (O k)) ∧ (∀ x ∈ A, ∃ k : s, x ∈ O k) ∧
      (∀ k (t : unitInterval) (a : ComplexPoint W), a ∈ A → G k (t, a) = a) ∧
      ∀ k (y : ComplexPoint W), y ∈ O k → R k y ∈ A := by
  classical
  let A := Set.range (Point.map j)
  letI : CompactSpace (ComplexPoint W) := persistence_finite_cover_compactSpace W B β
  have hA : IsCompact A := (isClosed_range_map_of_closedImmersion j).isCompact
  choose O hO hx R G hfixed hret using fun a : A =>
    persistence_finite_cover_closed_locus_global_patch W B E β j a.val a.property
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover O hO (by
    intro x hxA
    exact Set.mem_iUnion.mpr ⟨⟨x, hxA⟩, hx ⟨x, hxA⟩⟩)
  refine ⟨s, (fun k => O k.val), (fun k => R k.val), (fun k => G k.val),
    (fun k => hO k.val), ?_, (fun k => hfixed k.val), (fun k => hret k.val)⟩
  intro x hxA
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hs hxA)
  exact ⟨⟨a, ha⟩, hxa⟩

end HodgeLean.Foundations.QuotientDuality

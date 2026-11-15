import HodgeLean.Foundations.QuotientDuality.PersistenceSubspacePatch
import HodgeLean.Foundations.QuotientDuality.PersistenceChartNeighbourhood

/-! Global ambient homotopy patches from actual marked chart deformations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_marked_chart_global_patch
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {s : ℕ} {D : Fin s → Set X} (c : Marked.SubsetChart X D) (j : Fin s)
    (x : c.domain) (hx : x.val ∈ D j) :
    ∃ O : Set X, IsOpen O ∧ x.val ∈ O ∧ ∃ (R : C(X, X))
      (G : ContinuousMap.Homotopy (ContinuousMap.id X) R),
      (∀ (t : unitInterval) (a : X), a ∈ D j → G (t, a) = a) ∧
      ∀ y ∈ O, R y ∈ D j := by
  let a := complexEuclideanCoordinates c.n (c.coordinates x).val
  let V : Set c.domain := {y | complexEuclideanCoordinates c.n (c.coordinates y).val ∈
    Metric.closedBall a 1}
  let A : Set V := {y | y.val.val ∈ D j}
  obtain ⟨W, hW, hAW, q, hq, H, hfixed⟩ :=
    persistence_marked_chart_truncation_neighbourhood c j a 1 zero_le_one
  have hxV : x ∈ interior V := mem_interior_iff_mem_nhds.mpr
    (persistence_marked_chart_truncation_mem_nhds c x 1 zero_lt_one)
  have hxW : (⟨x, interior_subset hxV⟩ : V) ∈ W := hAW hx
  obtain ⟨U, hU, hxU, lift, hlift⟩ :=
    persistence_open_subspace_patch_domain V W hW x hxV hxW
  have hxdom : x.val ∈ interior (c.domain : Set X) := by
    rw [c.domain.isOpen.interior_eq]
    exact x.property
  obtain ⟨B, hB, hxB, liftB, hliftB⟩ :=
    persistence_open_subspace_patch_domain (c.domain : Set X) U hU x.val hxdom hxU
  let L : C(B, W) := lift.comp liftB
  have hL (u : B) : (L u).val.val.val = u.val :=
    (congrArg Subtype.val (hlift (liftB u))).trans (hliftB u)
  let incl : C(W, X) := ⟨fun w => w.val.val.val,
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)⟩
  let F : C(unitInterval × B, X) := incl.comp (H.toContinuousMap.comp
    ⟨fun p => (p.1, L p.2), continuous_fst.prodMk (L.continuous.comp continuous_snd)⟩)
  apply persistence_local_deformation_global_patch B (D j) hB F _ _ _ x.val hxB
  · intro u
    change incl (H (0, L u)) = u.val
    rw [H.apply_zero]
    exact hL u
  · intro t u hu
    have ha : (L u).val ∈ A := by
      change (L u).val.val.val ∈ D j
      rw [hL]
      exact hu
    have heq : H (t, L u) = L u := hfixed t ⟨(L u).val, ha⟩
    change incl (H (t, L u)) = u.val
    rw [heq]
    exact hL u
  · intro u
    change incl (H (1, L u)) ∈ D j
    rw [H.apply_one]
    exact (q (L u)).property

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.QuotientDuality.ProperCycleContractibleFaceChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenProductChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleFaceDimension
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicPositive

/-! # Actual full-target normal charts along geometric faces
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open CategoryTheory TopologicalSpace Topology HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original geometric face interior point has an actual centered full-target partial chart with contractible normal fibre and its precise original real tangential dimension.
Source: properCycle_geometric_complex_face_contractible_chart; properCycle_open_neighborhood_partial_chart; properCycle_selected_face_vector_finrank.
HC no distance; AV milestone no distance. -/
lemma properCycle_geometric_face_full_normal_chart {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (s : Finset E) (hs : s ∈ K.faces) (x : K.space)
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    let T : Finset V := Finset.univ.filter (fun a => a.val ∈ s)
    ∃ (j : T) (Y : TopCat.{0}) (y : Y)
      (b : OpenPartialHomeomorph K.space (properCycle_log_tangent j × Y)),
      ContractibleSpace Y ∧ b.target = Set.univ ∧ x ∈ b.source ∧ b x = (0, y) ∧
      Module.finrank ℝ (properCycle_log_tangent j) + 1 = s.card ∧
      (∀ z ∈ b.source, ∀ q ∈ K.faces, z.val ∈ convexHull ℝ (q : Set E) → s ⊆ q) ∧
      ∀ z ∈ b.source, z.val ∈ convexHull ℝ (s : Set E) ↔ (b z).2 = y := by
  classical
  dsimp only
  have hr : Set.range (fun i : s => (i.val : E)) = (s : Set E) := by
    ext z
    simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
  obtain ⟨u, hu⟩ := (s2v_hardt6rb_convexHull_range_weights _ x.val).mp
    (hr.symm ▸ intrinsicInterior_subset hx)
  have hpos : ∀ a : s, 0 < u.val a :=
    s2v_hardt6rb_intrinsicInterior_weights_pos (fun a : s => (a.val : E)) (K.indep hs) u
      (by rw [hu, hr]; exact hx)
  obtain ⟨j, U, Y, y, e, hY, hxU, hinc, hmark⟩ :=
    properCycle_geometric_complex_face_contractible_chart K hK V hV s hs u hpos x hu
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨b0, hb0s, hb0t, hb0val⟩ := properCycle_open_neighborhood_partial_chart
    (TopCat.of K.space) U _ e
  let t : (properCycle_log_tangent j × Y) ≃ₜ (properCycle_log_tangent j × Y) :=
    { toFun := fun z => (z.1 - (e ⟨x, hxU⟩).1, z.2)
      invFun := fun z => (z.1 + (e ⟨x, hxU⟩).1, z.2)
      left_inv := by intro z; exact Prod.ext (sub_add_cancel _ _) rfl
      right_inv := by intro z; exact Prod.ext (add_sub_cancel_right _ _) rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let b := b0.trans t.toOpenPartialHomeomorph
  have hbs : b.source = (U : Set K.space) := by
    change b0.source ∩ b0 ⁻¹' Set.univ = _
    rw [Set.preimage_univ, Set.inter_univ, hb0s]
  have hbt : b.target = Set.univ := by
    change Set.univ ∩ t.symm ⁻¹' b0.target = Set.univ
    rw [hb0t, Set.preimage_univ, Set.inter_univ]
  have hbval (z : U) : b z.val = t (e z) := by
    change t (b0 z.val) = t (e z)
    rw [hb0val]
  refine ⟨j, Y, y, b, hY, hbt, hbs ▸ hxU, ?_, ?_, ?_, ?_⟩
  · rw [hbval ⟨x, hxU⟩]
    change ((e ⟨x, hxU⟩).1 - (e ⟨x, hxU⟩).1, (e ⟨x, hxU⟩).2) = (0, y)
    rw [sub_self, (hmark ⟨x, hxU⟩).mp (intrinsicInterior_subset hx)]
  · apply properCycle_selected_face_vector_finrank V s ?_ j
    intro a ha
    exact hV a (K.down_closed hs (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty _))
  · intro z hz q hq hzq
    have hzU : z ∈ U := by
      rw [hbs] at hz
      exact hz
    exact hinc ⟨z, hzU⟩ q hq hzq
  · intro z hz
    have hzU : z ∈ U := by
      rw [hbs] at hz
      exact hz
    have hv := hbval ⟨z, hzU⟩
    have hn := congrArg Prod.snd hv
    change (b z).2 = (e ⟨z, hzU⟩).2 at hn
    rw [hn]
    exact hmark ⟨z, hzU⟩

end HodgeLean.Foundations.QuotientDuality

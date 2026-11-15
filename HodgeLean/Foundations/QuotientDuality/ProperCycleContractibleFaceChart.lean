import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexCoordinateSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleLabeledCarrier
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalCarrierConnected

/-! # Actual geometric face charts with contractible original normal fibres -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Interior points of actual finite geometric faces have constructed product charts whose original normal fibre is contractible.
Source: Munkres, Elements of Algebraic Topology, section 2, geometric complexes and barycentric star coordinates; properCycle_normal_carrier_contractible.
HC no distance; AV milestone no distance. -/
lemma properCycle_geometric_complex_face_contractible_chart {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (s : Finset E) (hs : s ∈ K.faces)
    (u : stdSimplex ℝ s) (hu : ∀ a : s, 0 < u.val a)
    (x : K.space) (hx : (∑ a : s, u.val a • a.val) = x.val) :
    let T : Finset V := Finset.univ.filter (fun a => a.val ∈ s)
    ∃ (j : T) (U : Opens K.space) (Y : TopCat.{0}) (y : Y)
      (e : U ≃ₜ (properCycle_log_tangent j × Y)),
      ContractibleSpace Y ∧ x ∈ U ∧
        (∀ z : U, ∀ q ∈ K.faces, z.val.val ∈ convexHull ℝ (q : Set E) → s ⊆ q) ∧
        ∀ z : U, z.val.val ∈ convexHull ℝ (s : Set E) ↔ (e z).2 = y := by
  classical
  dsimp only
  let T : Finset V := Finset.univ.filter (fun a => a.val ∈ s)
  obtain ⟨e0, hrec, hcoords⟩ := properCycle_finite_complex_weight_coordinates K hK V hV
  have hT : T.Nonempty := by
    obtain ⟨a, ha⟩ := K.nonempty_of_mem_faces hs
    have haV : a ∈ V := hV a
      (K.down_closed hs (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty _))
    exact ⟨⟨a, haV⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  have hpos : ∀ a ∈ T, 0 < (e0 x).val.val a := by
    intro a ha
    have has : a.val ∈ s := (Finset.mem_filter.mp ha).2
    rw [hcoords s hs u x hx a, dif_pos has]
    exact hu ⟨a.val, has⟩
  have hzero : ∀ a ∉ T, (e0 x).val.val a = 0 := by
    intro a ha
    have has : a.val ∉ s := fun h => ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [hcoords s hs u x hx a, dif_neg has]
  let p : ProperCycleFacePoint T := ⟨(e0 x).val, hpos, hzero⟩
  let j : T := ⟨hT.choose, hT.choose_spec⟩
  let G : Set (Finset V) := {t | ∃ q ∈ K.faces, t = Finset.univ.filter (fun a => a.val ∈ q)}
  have hTG : T ∈ G := ⟨s, hs, rfl⟩
  let Y := TopCat.of
    {v : ProperCycleNormalPoint T hT p | ∃ t ∈ G, ∀ a ∉ t, v.val.val.val a = 0}
  let y : Y := properCycle_carrier_normal_apex G T hT p hTG
  let U : Opens K.space :=
    ⟨{z | ∀ a ∈ T, 0 < (e0 z).val.val a},
      (properCycle_face_carrier_star_isOpen G T).preimage
        ((properCycle_labeled_carrier_homeomorph K.faces (fun a : V => a.val)).continuous.comp
          e0.continuous)⟩
  let eU : U ≃ₜ
      {w : {v : stdSimplex ℝ V | ∃ q ∈ K.faces, ∀ a : V, a.val ∉ q → v.val a = 0} |
        ∀ a ∈ T, 0 < w.val.val a} :=
    e0.subtype (fun _ => Iff.rfl)
  let ea := eU.trans (properCycle_labeled_star_homeomorph K.faces (fun a : V => a.val) T)
  let ec := properCycle_barycentric_vector_product G T hT p j
  let e : U ≃ₜ (properCycle_log_tangent j × Y) := ea.trans ec
  have hinc (z : U) (q : Finset E) (hq : q ∈ K.faces)
      (hzq : z.val.val ∈ convexHull ℝ (q : Set E)) : s ⊆ q := by
    let W : C(K.space, stdSimplex ℝ V) :=
      ⟨fun z => (e0 z).val, continuous_subtype_val.comp e0.continuous⟩
    have hF := (properCycle_complex_coordinates_face_iff K V W hrec hcoords q hq z.val).mp hzq
    intro a ha
    have haV : a ∈ V := hV a
      (K.down_closed hs (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty _))
    by_contra hnot
    have hzero := hF ⟨a, haV⟩ hnot
    have hpositive := z.property ⟨a, haV⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
    exact (ne_of_gt hpositive) hzero
  refine ⟨j, U, Y, y, e, properCycle_normal_carrier_contractible G T hT p hTG, hpos, hinc, ?_⟩
  intro z
  have hm := properCycle_barycentric_vector_product_mark G T hT p j hTG (ea z)
  change z.val.val ∈ convexHull ℝ (s : Set E) ↔
    (properCycle_barycentric_vector_product G T hT p j (ea z)).2 =
      properCycle_carrier_normal_apex G T hT p hTG
  rw [hm]
  change z.val.val ∈ convexHull ℝ (s : Set E) ↔ ∀ a ∉ T, (e0 z.val).val.val a = 0
  let W : C(K.space, stdSimplex ℝ V) :=
    ⟨fun z => (e0 z).val, continuous_subtype_val.comp e0.continuous⟩
  have hF := properCycle_complex_coordinates_face_iff K V W hrec hcoords s hs z.val
  constructor
  · intro hz a ha
    apply hF.mp hz a
    exact fun h => ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  · intro hz
    apply hF.mpr
    intro a ha
    apply hz a
    simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using ha

end HodgeLean.Foundations.QuotientDuality

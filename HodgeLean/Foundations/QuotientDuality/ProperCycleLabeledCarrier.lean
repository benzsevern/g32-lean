import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricMarkedChart

/-! # Actual face carriers under finite vertex labels -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]

/-- Labelled supporting faces describe exactly the corresponding actual subsets of the finite vertex index set.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates of geometric complexes.
HC no distance; AV milestone no distance. -/
lemma properCycle_labeled_face_carrier_iff (F : Set (Finset α)) (v : ι → α)
    (w : stdSimplex ℝ ι) :
    (∃ s ∈ F, ∀ i, v i ∉ s → w.val i = 0) ↔
      ∃ t ∈ ({t | ∃ s ∈ F, t = Finset.univ.filter (fun i => v i ∈ s)} : Set (Finset ι)),
        ∀ i ∉ t, w.val i = 0 := by
  constructor
  · rintro ⟨s, hs, hw⟩
    refine ⟨Finset.univ.filter (fun i => v i ∈ s), ⟨s, hs, rfl⟩, ?_⟩
    intro i hi
    apply hw i
    exact fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
  · rintro ⟨t, ⟨s, hs, rfl⟩, hw⟩
    refine ⟨s, hs, fun i hi => hw i ?_⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi

/-- Relabelling actual supporting faces gives the identity homeomorphism on their barycentric carrier.
Source: Munkres, Elements of Algebraic Topology, section 2, finite barycentric coordinate carriers.
HC no distance; AV milestone no distance. -/
def properCycle_labeled_carrier_homeomorph (F : Set (Finset α)) (v : ι → α) :
    {w : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i, v i ∉ s → w.val i = 0} ≃ₜ
      {w : stdSimplex ℝ ι |
        ∃ t ∈ ({t | ∃ s ∈ F, t = Finset.univ.filter (fun i => v i ∈ s)} : Set (Finset ι)),
          ∀ i ∉ t, w.val i = 0} :=
  Homeomorph.setCongr (Set.ext (fun w => properCycle_labeled_face_carrier_iff F v w))

/-- The identity carrier relabelling retains the literal open-star constraints.
Source: Munkres, Elements of Algebraic Topology, section 2, finite barycentric coordinate carriers.
HC no distance; AV milestone no distance. -/
def properCycle_labeled_star_homeomorph (F : Set (Finset α)) (v : ι → α) (S : Finset ι) :
    {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i, v i ∉ s → u.val i = 0} |
      ∀ i ∈ S, 0 < w.val.val i} ≃ₜ
      {w : {u : stdSimplex ℝ ι |
        ∃ t ∈ ({t | ∃ s ∈ F, t = Finset.univ.filter (fun i => v i ∈ s)} : Set (Finset ι)),
          ∀ i ∉ t, u.val i = 0} | ∀ i ∈ S, 0 < w.val.val i} :=
  (properCycle_labeled_carrier_homeomorph F v).subtype
    (p := fun w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i, v i ∉ s → u.val i = 0} =>
      ∀ i ∈ S, 0 < w.val.val i)
    (q := fun w : {u : stdSimplex ℝ ι |
      ∃ t ∈ ({t | ∃ s ∈ F, t = Finset.univ.filter (fun i => v i ∈ s)} : Set (Finset ι)),
        ∀ i ∉ t, u.val i = 0} => ∀ i ∈ S, 0 < w.val.val i) (fun _ => Iff.rfl)

end HodgeLean.Foundations.QuotientDuality

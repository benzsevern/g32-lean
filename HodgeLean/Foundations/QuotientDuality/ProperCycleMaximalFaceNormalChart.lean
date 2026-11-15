import HodgeLean.Foundations.QuotientDuality.ProperCycleFaceFullNormalChart

/-! # Actual full-support normal charts at maximal geometric faces
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- At an original maximal support face the actual centered contractible-normal chart flattens the entire original subcomplex support, with its precise real face dimension.
Source: properCycle_geometric_face_full_normal_chart; Geometry.SimplicialComplex.mem_space_iff; maximal-face incidence.
HC no distance; AV milestone no distance. -/
lemma properCycle_maximal_face_full_support_normal_chart {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces) (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (s : Finset E) (hs : s ∈ D.faces)
    (hmax : ∀ q ∈ D.faces, s ⊆ q → q = s) (x : K.space)
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    let T : Finset V := Finset.univ.filter (fun a => a.val ∈ s)
    ∃ (j : T) (Y : TopCat.{0}) (y : Y)
      (b : OpenPartialHomeomorph K.space (properCycle_log_tangent j × Y)),
      ContractibleSpace Y ∧ b.target = Set.univ ∧ x ∈ b.source ∧ b x = (0, y) ∧
      Module.finrank ℝ (properCycle_log_tangent j) + 1 = s.card ∧
      ∀ z ∈ b.source, z.val ∈ D.space ↔ (b z).2 = y := by
  obtain ⟨j, Y, y, b, hY, htarget, hxb, hcenter, hdim, hinc, hflat⟩ :=
    properCycle_geometric_face_full_normal_chart K hK V hV s (hDK hs) x hx
  refine ⟨j, Y, y, b, hY, htarget, hxb, hcenter, hdim, ?_⟩
  intro z hz
  constructor
  · intro hzD
    obtain ⟨q, hq, hzq⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hzD
    have heq : q = s := hmax q hq (hinc z hz q (hDK hq) hzq)
    apply (hflat z hz).mp
    simpa only [heq] using hzq
  · intro hn
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, hs, (hflat z hz).mpr hn⟩

end HodgeLean.Foundations.QuotientDuality

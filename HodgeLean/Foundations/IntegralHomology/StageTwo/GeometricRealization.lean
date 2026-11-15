import HodgeLean.Foundations.IntegralHomology.StageTwo.GeometricCoordinates
import HodgeLean.Foundations.IntegralHomology.StageTwo.BarycentricHull

/-! Realization of the ordered model of a finite geometric complex.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Convexity
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

variable {E : Type} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem indexed_barycentricPoint_mem {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) (v : Fin (n + 1) → E)
    (p : faceCoordinateSpace (indexedFaces K v)) : barycentricPoint v p.val ∈ K.space := by
  obtain ⟨s, hs, hp⟩ := p.property
  obtain ⟨u, _, hpoint⟩ := supported_distribution v p.val s hp
  apply Geometry.SimplicialComplex.mem_space_iff.mpr
  refine ⟨s.image v, hs, ?_⟩
  rw [← hpoint]
  exact barycentricPoint_mem_convexHull (fun a : s.image v => a.val) u _
    (fun a => a.property)

def coordinateToGeometric {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) (v : Fin (n + 1) → E) :
    C(faceCoordinateSpace (indexedFaces K v), K.space) :=
  ⟨fun p => ⟨barycentricPoint v p.val, indexed_barycentricPoint_mem K v p⟩,
    ((continuous_barycentricPoint v).comp continuous_subtype_val).subtype_mk _⟩

theorem coordinateToGeometric_injective [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (v : Fin (n + 1) → E) (hv : Function.Injective v) :
    Function.Injective (coordinateToGeometric K v) := by
  obtain ⟨c, hc⟩ := indexed_geometric_coordinate_recovery K hK v hv
  intro p q h
  apply Subtype.ext
  apply StdSimplex.ext
  apply Finsupp.ext
  intro i
  rw [← hc p i, ← hc q i]
  exact congrArg (c (v i)) (congrArg Subtype.val h)

theorem coordinateToGeometric_surjective {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) (v : Fin (n + 1) → E)
    (hV : K.vertices ⊆ Set.range v) : Function.Surjective (coordinateToGeometric K v) := by
  classical
  intro x
  obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.property
  obtain ⟨t, ht⟩ := indexedFaces_image_contains K v hV s hs
  have hr : Set.range (fun a : s => (a.val : E)) = (s : Set E) := by
    ext a
    simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
  have hm : x.val ∈ Set.range (barycentricPoint (fun a : s => (a.val : E))) := by
    rw [barycentricPoint_range, hr]
    exact hx
  obtain ⟨w, hw⟩ := hm
  have hex (a : s) : ∃ i : Fin (n + 1), i ∈ t ∧ v i = a.val := by
    have ha : a.val ∈ t.image v := ht.symm ▸ a.property
    exact Finset.mem_image.mp ha
  choose f hfm hfv using hex
  have hp (i : Fin (n + 1)) (hi : i ∉ t) : (w.map f).weights i = 0 :=
    (StdSimplex.mem_range_map_iff f (w.map f)).mp ⟨w, rfl⟩ i (by
      rintro ⟨a, rfl⟩
      exact hi (hfm a))
  let p : faceCoordinateSpace (indexedFaces K v) :=
    ⟨w.map f, t, by change t.image v ∈ K.faces; rw [ht]; exact hs, hp⟩
  refine ⟨p, Subtype.ext ?_⟩
  change barycentricPoint v (w.map f) = x.val
  rw [barycentricPoint_map]
  have hfun : (fun a : s => v (f a)) = (fun a : s => a.val) := funext hfv
  rw [hfun]
  exact hw

def geometricCoordinateHomeomorph [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (v : Fin (n + 1) → E) (hv : Function.Injective v)
    (hV : K.vertices ⊆ Set.range v) :
    faceCoordinateSpace (indexedFaces K v) ≃ₜ K.space := by
  haveI := realized_face_complex_compact (indexedFaces K v)
  letI : CompactSpace (faceCoordinateSpace (indexedFaces K v)) :=
    (faceCoordinateHomeomorph (indexedFaces K v)).compactSpace
  let e := Equiv.ofBijective (coordinateToGeometric K v)
    ⟨coordinateToGeometric_injective K hK v hv, coordinateToGeometric_surjective K v hV⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := e) (coordinateToGeometric K v).continuous

def indexedGeometricRealizationHomeomorph [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (v : Fin (n + 1) → E) (hv : Function.Injective v)
    (hV : K.vertices ⊆ Set.range v) :
    SSet.toTop.obj (faceComplex (indexedFaces K v) : SSet.{0}) ≃ₜ K.space :=
  (faceCoordinateHomeomorph (indexedFaces K v)).trans
    (geometricCoordinateHomeomorph K hK v hv hV)

end HodgeLean.Foundations.IntegralHomology.StageTwo

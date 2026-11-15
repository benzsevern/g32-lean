import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicSimplex
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-! Every geometric complex carrier point belongs to an actual intrinsic open face. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_mem_open_face {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) {x : E} (hx : x ∈ K.space) :
    ∃ T ∈ K.faces, x ∈ intrinsicInterior ℝ (convexHull ℝ (↑T : Set E)) := by
  classical
  obtain ⟨S, hS, hxS⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  have hSrange : Set.range (fun i : S => (i.val : E)) = (↑S : Set E) := by
    ext y
    simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
  rw [← hSrange] at hxS
  obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights _ x).mp hxS
  let I : Finset S := Finset.univ.filter (fun i => 0 < w.val i)
  have hzero (i : S) (hi : i ∉ I) : w.val i = 0 := by
    have hn : ¬ 0 < w.val i := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact le_antisymm (le_of_not_gt hn) (w.property.1 i)
  have hsumI : (∑ i ∈ I, w.val i) = 1 :=
    (Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hzero i hi)).trans w.property.2
  have hI : I.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he, Finset.sum_empty] at hsumI
    exact zero_ne_one hsumI
  have hsum : (∑ i : I, w.val i.val) = 1 := by
    rw [Finset.univ_eq_attach, Finset.sum_attach I w.val]
    exact hsumI
  let u : stdSimplex ℝ I := ⟨(fun i => w.val i.val), (fun i => w.property.1 i.val), hsum⟩
  have hup : ∀ i : I, 0 < u.val i := fun i => (Finset.mem_filter.mp i.property).2
  have hpoint : (∑ i : I, u.val i • i.val.val) = x := by
    change (∑ i : I, w.val i.val • i.val.val) = x
    rw [Finset.univ_eq_attach, Finset.sum_attach I (fun i : S => w.val i • i.val)]
    have he := Finset.sum_subset (Finset.subset_univ I)
      (fun i _ hi => show w.val i • i.val = 0 by rw [hzero i hi, zero_smul])
    exact he.trans hw
  let T : Finset E := I.image (fun i : S => i.val)
  have hTS : T ⊆ S := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact i.property
  have hT : T.Nonempty := by
    obtain ⟨i, hi⟩ := hI
    exact ⟨i.val, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  have hrange : Set.range (fun i : I => (i.val.val : E)) = (↑T : Set E) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩
    · intro hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨⟨i, hi⟩, rfl⟩
  have hop := s2v_hardt6rb_positive_weights_mem_intrinsicInterior (fun i : I => i.val.val) u hup
  rw [hrange] at hop
  exact ⟨T, K.down_closed hS hTS hT, hpoint ▸ hop⟩

end HodgeLean.Foundations.Program

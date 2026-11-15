import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairNormalizedPoint
import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairPositiveMassPath
import Mathlib.Topology.Homotopy.Basic

/-! Open-star deformations of full finite geometric subcomplexes.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- A full subcomplex has a positive-mass neighbourhood with a fixed straight-line deformation. -/
theorem s2e_pair_full_star_deformation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces)
    (hfull : ∀ s ∈ K.faces, (∀ a ∈ s, a ∈ D.vertices) → s ∈ D.faces)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V) :
    ∃ U : Set K.space, IsOpen U ∧
      (∀ x : K.space, x.val ∈ D.space → x ∈ U) ∧
      ∃ r : C(U, U),
        (∀ x : U, (r x).val.val ∈ D.space) ∧
        (∀ x : U, x.val.val ∈ D.space → r x = x) ∧
        ∃ H : ContinuousMap.Homotopy (ContinuousMap.id U) r,
          ∀ (t : unitInterval) (x : U), x.val.val ∈ D.space → H (t, x) = x := by
  classical
  obtain ⟨W, hrec, hW⟩ := s2e_pair_barycentric_map K hK V hV
  let S : Finset V := Finset.univ.filter (fun a => a.val ∈ D.vertices)
  have hS (a : V) : a ∈ S ↔ a.val ∈ D.vertices := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  let mass : K.space → ℝ := fun x => ∑ a ∈ S, (W x).val a
  have hmass : Continuous mass := continuous_finsetSum S (fun a _ =>
    (continuous_apply a).comp (continuous_subtype_val.comp W.continuous))
  let U : Set K.space := {x | 0 < mass x}
  have hU : IsOpen U := isOpen_lt continuous_const hmass
  have hsV (s : Finset E) (hs : s ∈ K.faces) : s ⊆ V := by
    intro a ha
    exact hV a (K.down_closed hs (Finset.singleton_subset_iff.mpr ha)
      (Finset.singleton_nonempty _))
  have hweights (L : Geometry.SimplicialComplex ℝ E) (x : E) (hx : x ∈ L.space) :
      ∃ (s : Finset E) (hs : s ∈ L.faces) (w : stdSimplex ℝ s),
        (∑ i, w.val i • i.val) = x := by
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    have hr : Set.range (fun i : s => (i.val : E)) = (↑s : Set E) := by
      ext z
      simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
    obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights _ x).mp (hr.symm ▸ hxs)
    exact ⟨s, hs, w, hw⟩
  have hmarked (x : K.space) (hx : x.val ∈ D.space) :
      ∀ a : V, a ∉ S → (W x).val a = 0 := by
    obtain ⟨s, hs, u, hu⟩ := hweights D x.val hx
    intro a ha
    have has : a.val ∉ s := by
      intro has
      apply ha
      apply (hS a).mpr
      exact D.down_closed hs (Finset.singleton_subset_iff.mpr has)
        (Finset.singleton_nonempty _)
    rw [hW s (hDK hs) u x hu a, dite_eq_right has]
  have hmarkedmass (x : K.space) (hx : x.val ∈ D.space) : mass x = 1 := by
    change (∑ a ∈ S, (W x).val a) = 1
    rw [← (W x).property.2]
    exact Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hmarked x hx a ha)
  have hcontains (x : K.space) (hx : x.val ∈ D.space) : x ∈ U := by
    change 0 < mass x
    rw [hmarkedmass x hx]
    exact zero_lt_one
  let N : C(U, stdSimplex ℝ V) := (s2e_pair_faceNormalizeMap S).comp
    { toFun := fun x => ⟨W x.val, x.property⟩
      continuous_toFun := (W.continuous.comp continuous_subtype_val).subtype_mk _ }
  let F : C(U, E) :=
    { toFun := fun x => ∑ a : V, (N x).val a • a.val
      continuous_toFun := continuous_finsetSum Finset.univ (fun a _ =>
        ((continuous_apply a).comp (continuous_subtype_val.comp N.continuous)).smul
          continuous_const) }
  have hF (x : U) : ∃ y : K.space, y.val = F x ∧ W y = N x ∧ y.val ∈ D.space := by
    obtain ⟨s, hs, u, hu⟩ := hweights K x.val.val x.val.property
    have hsupport (a : V) (ha : a.val ∉ s) : (W x.val).val a = 0 := by
      rw [hW s hs u x.val hu a, dite_eq_right ha]
    exact s2e_pair_normalized_point K D V W hW hfull S hS s hs (hsV s hs)
      (W x.val) hsupport x.property
  let rfun : U → U := fun x =>
    ⟨(hF x).choose, by
      change 0 < ∑ a ∈ S, (W (hF x).choose).val a
      rw [(hF x).choose_spec.2.1]
      change 0 < ∑ a ∈ S, (s2e_pair_faceNormalize S (W x.val) x.property).val a
      rw [s2e_pair_faceNormalize_selected_total]
      exact zero_lt_one⟩
  have hrval (x : U) : (rfun x).val.val = F x := (hF x).choose_spec.1
  let r : C(U, U) :=
    { toFun := rfun
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        convert F.continuous using 1
        exact funext hrval }
  have hrmarked (x : U) : (r x).val.val ∈ D.space := (hF x).choose_spec.2.2
  have hrfixed (x : U) (hx : x.val.val ∈ D.space) : r x = x := by
    apply Subtype.ext
    apply Subtype.ext
    change (rfun x).val.val = x.val.val
    rw [hrval]
    change (∑ a : V, (s2e_pair_faceNormalize S (W x.val) x.property).val a • a.val) = _
    rw [s2e_pair_faceNormalize_fixed S (W x.val) x.property (hmarked x.val hx)]
    exact hrec x.val
  have hpath (t : unitInterval) (x : U) : ∃ y : U,
      y.val.val = (1 - (t : ℝ)) • x.val.val + (t : ℝ) • (r x).val.val := by
    obtain ⟨s, hs, u, hu⟩ := hweights K x.val.val x.val.property
    have hsupport (a : V) (ha : a.val ∉ s) : (W x.val).val a = 0 := by
      rw [hW s hs u x.val hu a, dite_eq_right ha]
    obtain ⟨y, hy, hpos⟩ := s2e_pair_positive_mass_path K V W hW s hs (hsV s hs)
      (W x.val) hsupport S x.property t
    refine ⟨⟨y, hpos⟩, ?_⟩
    rw [hy, hrec]
    change (1 - (t : ℝ)) • x.val.val + (t : ℝ) • F x = _
    rw [← hrval]
    rfl
  let H : ContinuousMap.Homotopy (ContinuousMap.id U) r :=
    { toFun := fun p => (hpath p.1 p.2).choose
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        change Continuous (fun p : unitInterval × U => ((hpath p.1 p.2).choose).val.val)
        have he : (fun p : unitInterval × U => ((hpath p.1 p.2).choose).val.val) =
            fun p => (1 - (p.1 : ℝ)) • p.2.val.val + (p.1 : ℝ) • (r p.2).val.val :=
          funext (fun p => (hpath p.1 p.2).choose_spec)
        rw [he]
        exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).add
          ((continuous_subtype_val.comp continuous_fst).smul
            (continuous_subtype_val.comp (continuous_subtype_val.comp
              (r.continuous.comp continuous_snd))))
      map_zero_left := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        change ((hpath 0 x).choose).val.val = x.val.val
        rw [(hpath 0 x).choose_spec]
        change (1 - (0 : ℝ)) • x.val.val + (0 : ℝ) • (r x).val.val = x.val.val
        simp only [sub_zero, one_smul, zero_smul, add_zero]
      map_one_left := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        change ((hpath 1 x).choose).val.val = (r x).val.val
        rw [(hpath 1 x).choose_spec]
        change (1 - (1 : ℝ)) • x.val.val + (1 : ℝ) • (r x).val.val = (r x).val.val
        simp only [sub_self, zero_smul, one_smul, zero_add] }
  refine ⟨U, hU, hcontains, r, hrmarked, hrfixed, H, ?_⟩
  intro t x hx
  apply Subtype.ext
  apply Subtype.ext
  change ((hpath t x).choose).val.val = x.val.val
  rw [(hpath t x).choose_spec, hrfixed x hx, ← add_smul, sub_add_cancel, one_smul]

end Semialgebraic.CompatibleTriangulation.Helpers

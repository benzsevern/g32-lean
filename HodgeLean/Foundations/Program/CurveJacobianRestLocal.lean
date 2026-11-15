import HodgeLean.Foundations.Program.CurveJacobianFormsBasic

/-! # Track B3, lane Rest: forms built in one chart

`b3Rest_ofLoc x A` is the family of forms on `M` whose local representative in the chart at `x`
is `A` (a field of alternating maps on the chart image), extended by `0` outside the chart
domain. When `A` is smooth with compact support inside the chart image, it is a smooth form
(`b3Rest_isSmooth_ofLoc`), and its local representative in any chart is the pullback of `A` along
the change of coordinates (`b3Rest_loc_ofLoc`).
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

open scoped Classical in
/-- **The form with local representative `A` in the chart at `x`**, extended by zero. -/
def b3Rest_ofLoc (x : M) (A : E → E [⋀^Fin k]→L[ℝ] ℝ) : M → E [⋀^Fin k]→L[ℝ] ℝ := fun p ↦
  if p ∈ (chartAt E x).source then
    (A (chartAt E x p)).compContinuousLinearMap (fderiv ℝ (b3Forms_tr p x) (chartAt E p p))
  else 0

theorem b3Rest_loc_ofLoc (x : M) (A : E → E [⋀^Fin k]→L[ℝ] ℝ) {y : M} {v : E}
    (hv : v ∈ (chartAt E y).target) (hp : (chartAt E y).symm v ∈ (chartAt E x).source) :
    b3Forms_loc (b3Rest_ofLoc x A) y v =
      (A (b3Forms_tr y x v)).compContinuousLinearMap (fderiv ℝ (b3Forms_tr y x) v) := by
  set p := (chartAt E y).symm v
  have hv' : v ∈ b3Forms_trDom y p := b3Forms_mem_trDom_self hv
  have htr : b3Forms_tr y p v = chartAt E p p := rfl
  have hval : b3Rest_ofLoc x A p = (A (chartAt E x p)).compContinuousLinearMap
      (fderiv ℝ (b3Forms_tr p x) (chartAt E p p)) := by simp [b3Rest_ofLoc, hp]
  have hloc : b3Forms_loc (b3Rest_ofLoc x A) y v =
      (b3Rest_ofLoc x A p).compContinuousLinearMap (fderiv ℝ (b3Forms_tr y p) v) := rfl
  rw [hloc, hval, b3Forms_fderiv_tr_comp (z := x) hv' hp, htr]
  ext w
  rfl

theorem b3Rest_loc_ofLoc_of_notMem (x : M) (A : E → E [⋀^Fin k]→L[ℝ] ℝ) {y : M} {v : E}
    (hp : (chartAt E y).symm v ∉ (chartAt E x).source) :
    b3Forms_loc (b3Rest_ofLoc x A) y v = 0 := by
  have hval : b3Rest_ofLoc x A ((chartAt E y).symm v) = 0 := by simp [b3Rest_ofLoc, hp]
  have hloc : b3Forms_loc (b3Rest_ofLoc x A) y v =
      (b3Rest_ofLoc x A ((chartAt E y).symm v)).compContinuousLinearMap
        (fderiv ℝ (b3Forms_tr y ((chartAt E y).symm v)) v) := rfl
  rw [hloc, hval]
  ext w
  simp

/-- The local representative of `b3Rest_ofLoc x A` in the chart at `x` is `A`. -/
theorem b3Rest_loc_ofLoc_self (x : M) (A : E → E [⋀^Fin k]→L[ℝ] ℝ) {v : E}
    (hv : v ∈ (chartAt E x).target) : b3Forms_loc (b3Rest_ofLoc x A) x v = A v := by
  rw [b3Rest_loc_ofLoc x A hv ((chartAt E x).map_target hv), b3Forms_fderiv_tr_self hv]
  have : b3Forms_tr x x v = v := (chartAt E x).right_inv hv
  rw [this]
  ext w
  simp

/-- **A compactly supported smooth field in a chart gives a smooth form.** -/
theorem b3Rest_isSmooth_ofLoc [FiniteDimensional ℝ E] [T2Space M] (x : M) {A : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (hs : tsupport A ⊆ (chartAt E x).target) :
    b3Forms_IsSmooth (b3Rest_ofLoc x A) := by
  intro y
  set S : Set M := (chartAt E x).symm '' tsupport A
  have hSc : IsCompact S := hc.isCompact.image_of_continuousOn
    ((chartAt E x).continuousOn_symm.mono hs)
  refine contDiffOn_of_locally_contDiffOn fun v hv ↦ ?_
  by_cases hp : (chartAt E y).symm v ∈ (chartAt E x).source
  · refine ⟨b3Forms_trDom y x, b3Forms_isOpen_trDom y x, ⟨hv, hp⟩, ?_⟩
    have h1 : ContDiffOn ℝ ∞ (fun w ↦ A (b3Forms_tr y x w)) (b3Forms_trDom y x) :=
      hA.comp_contDiffOn (b3Forms_contDiffOn_tr y x)
    have h2 : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ (b3Forms_tr (E := E) y x) w) (b3Forms_trDom y x) :=
      (b3Forms_contDiffOn_tr y x).fderiv_of_isOpen (b3Forms_isOpen_trDom y x) (by simp)
    have h3 : ContDiffOn ℝ ∞ (fun w ↦ (A (b3Forms_tr y x w)).compContinuousLinearMap
        (fderiv ℝ (b3Forms_tr (E := E) y x) w)) (b3Forms_trDom y x) :=
      b3Forms_contDiffOn_comp h1 h2
    refine (h3.congr fun w hw ↦ ?_).mono inter_subset_right
    exact b3Rest_loc_ofLoc x A hw.1 hw.2
  · set W := (chartAt E y).target ∩ (chartAt E y).symm ⁻¹' Sᶜ
    have hWo : IsOpen W := (chartAt E y).continuousOn_symm.isOpen_inter_preimage
      (chartAt E y).open_target hSc.isClosed.isOpen_compl
    have hvW : v ∈ W := by
      refine ⟨hv, fun hS ↦ hp ?_⟩
      obtain ⟨u, hu, hu'⟩ := hS
      rw [← hu']
      exact (chartAt E x).map_target (hs hu)
    refine ⟨W, hWo, hvW, (contDiffOn_const (c := 0)).congr fun w hw ↦ ?_⟩
    by_cases hp' : (chartAt E y).symm w ∈ (chartAt E x).source
    · rw [b3Rest_loc_ofLoc x A hw.1 hp']
      have hnot : b3Forms_tr y x w ∉ tsupport A := by
        intro hmem
        apply hw.2.2
        refine ⟨b3Forms_tr y x w, hmem, ?_⟩
        exact b3Forms_symm_tr (x := y) (y := x) ⟨hw.1, hp'⟩
      rw [image_eq_zero_of_notMem_tsupport hnot]
      ext u
      simp
    · exact b3Rest_loc_ofLoc_of_notMem x A hp'

end HodgeLean.Foundations.Program

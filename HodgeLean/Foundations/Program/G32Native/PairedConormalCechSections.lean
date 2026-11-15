import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Sections.SectionsGluing
import Mathlib.Tactic.FinCases
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf

/-! # Global sections from the actual degree-zero ordered Cech cocycles -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

variable {R : Type} [CommRing R] {X : Scheme} {π : X ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : X.OrderedAffineCover)

/-- Equal vertices give equal restricted values with the actual restriction
proofs retained, including their dependent section types. -/
theorem paired_cech_res_eq_of_vertex_eq (c : F.cochain K 0)
    (s t : K.Idx 0) (hst : s = t) (W : X.Opens)
    (hWs : W ≤ K.inter s) (hWt : W ≤ K.inter t) :
    F.res hWs (c s) = F.res hWt (c t) := by
  subst t
  rfl

/-- A degree-zero cocycle agrees on every smaller open for an ordered pair
of chart vertices. The equation is the actual first Cech differential. -/
theorem paired_cech_zero_compatible_of_lt
    (c : F.cochain K 0) (hc : F.d K 0 c = 0) (s t : K.Idx 0)
    (hst : s.1 0 < t.1 0) (W : X.Opens)
    (hWs : W ≤ K.inter s) (hWt : W ≤ K.inter t) :
    F.res hWs (c s) = F.res hWt (c t) := by
  let e : K.Idx 1 := ⟨![s.1 0, t.1 0], by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact (lt_irrefl _ hab).elim
    · exact hst
    · exact (by norm_num at hab)
    · exact (lt_irrefl _ hab).elim⟩
  have hface₀ : K.face e 0 = t := by
    apply Subtype.ext
    funext i
    fin_cases i
    rfl
  have hface₁ : K.face e 1 = s := by
    apply Subtype.ext
    funext i
    fin_cases i
    rfl
  have hW : W ≤ K.inter e := by
    apply le_iInf
    intro j
    fin_cases j
    · exact hWs.trans (K.inter_le s 0)
    · exact hWt.trans (K.inter_le t 0)
  have hz := congrFun hc e
  rw [F.d_apply, Fin.sum_univ_two] at hz
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
    neg_one_zsmul, Pi.zero_apply] at hz
  have heq :
      F.res (K.inter_le_inter_face e 1) (c (K.face e 1)) =
        F.res (K.inter_le_inter_face e 0) (c (K.face e 0)) := by
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg] using hz
  have h := congrArg (F.res hW) heq
  rw [F.res_res, F.res_res] at h
  exact (paired_cech_res_eq_of_vertex_eq F K c _ _ hface₁ W _ hWs).symm.trans
    (h.trans (paired_cech_res_eq_of_vertex_eq F K c _ _ hface₀ W _ hWt))

/-- Every degree-zero cocycle is compatible on every pairwise restriction. -/
theorem paired_cech_zero_compatible
    (c : F.cochain K 0) (hc : F.d K 0 c = 0) (s t : K.Idx 0)
    (W : X.Opens) (hWs : W ≤ K.inter s) (hWt : W ≤ K.inter t) :
    F.res hWs (c s) = F.res hWt (c t) := by
  rcases lt_trichotomy (s.1 0) (t.1 0) with h | h | h
  · exact paired_cech_zero_compatible_of_lt F K c hc s t h W hWs hWt
  · have he : s = t := by
      apply Subtype.ext
      funext i
      fin_cases i
      exact h
    exact paired_cech_res_eq_of_vertex_eq F K c s t he W hWs hWt
  · exact (paired_cech_zero_compatible_of_lt F K c hc t s h W hWt hWs).symm

/-- The actual singleton simplex at a specified affine chart. -/
def pairedCechVertex (i : K.ι) : K.Idx 0 :=
  ⟨fun _ => i, by
    intro a b h
    fin_cases a
    fin_cases b
    exact (lt_irrefl _ h).elim⟩

/-- The singleton simplex retains its original chart open. -/
theorem pairedCechVertex_inter (i : K.ι) : K.inter (pairedCechVertex K i) = K.U i := by
  simp only [Scheme.OrderedAffineCover.inter, pairedCechVertex, iInf_const]

/-- The actual degree-zero intersections still cover the whole scheme. -/
theorem paired_cech_vertex_cover : (⨆ s : K.Idx 0, K.inter s) = ⊤ := by
  apply le_antisymm le_top
  rw [← K.iSup_eq_top]
  apply iSup_le
  intro i
  rw [← pairedCechVertex_inter K i]
  exact le_iSup (fun s : K.Idx 0 => K.inter s) (pairedCechVertex K i)

/-- A cocycle for an actual module sheaf glues to an actual global section,
retaining every original degree-zero restriction. -/
theorem paired_cech_zero_glue (M : X.Modules)
    (c : (Scheme.Modules.toOModulePresheaf π M).cochain K 0)
    (hc : (Scheme.Modules.toOModulePresheaf π M).d K 0 c = 0) :
    ∃ z : Γ(M, ⊤), ∀ s : K.Idx 0,
      M.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op z = c s := by
  apply (Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    M (fun s : K.Idx 0 => K.inter s) ⊤ (fun _ => le_top)
      (by rw [paired_cech_vertex_cover K])).2 c
  intro s t
  exact paired_cech_zero_compatible (Scheme.Modules.toOModulePresheaf π M) K c hc
    s t (K.inter s ⊓ K.inter t) inf_le_left inf_le_right

/-- Restriction of an actual global element to the original intersections. -/
def pairedCechRestriction (z : F.obj ⊤) : F.cochain K 0 :=
  fun s => F.res (le_top : K.inter s ≤ ⊤) z

/-- Actual restrictions satisfy the original first Cech differential. -/
theorem pairedCechRestriction_cocycle (z : F.obj ⊤) :
    F.d K 0 (pairedCechRestriction F K z) = 0 := by
  funext s
  rw [F.d_apply, Fin.sum_univ_two]
  simp only [pairedCechRestriction, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul, F.res_res, add_neg_cancel, Pi.zero_apply]

end HodgeLean.Foundations.Program.G32Native

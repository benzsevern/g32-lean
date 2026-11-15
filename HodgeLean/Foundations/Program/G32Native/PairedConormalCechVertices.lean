import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Mathlib.Tactic.FinCases

/-! # Degree-zero coordinates for the ordered affine cover complex -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native

variable {R : Type*} [CommRing R] {X : Scheme} {f : X ⟶ Spec (.of R)}
    (F : OModulePresheaf f) (K : X.OrderedAffineCover)

def conormalCechVertex (i : K.ι) : K.Idx 0 :=
  ⟨fun _ => i, fun a b h => False.elim (by omega)⟩

theorem conormalCechVertex_inter (i : K.ι) :
    K.inter (conormalCechVertex K i) = K.U i := by
  simp only [Scheme.OrderedAffineCover.inter, conormalCechVertex, iInf_const]

def conormalCechVertexSection (c : F.cochain K 0) (i : K.ι) : F.obj (K.U i) :=
  F.res (by rw [conormalCechVertex_inter]) (c (conormalCechVertex K i))

/-- A zero cocycle gives compatible sections on the original affine opens. -/
theorem conormalCechVertexSection_compatible (c : F.H0 K) (i j : K.ι) :
    F.res (inf_le_left : K.U i ⊓ K.U j ≤ K.U i) (conormalCechVertexSection F K c.val i) =
    F.res (inf_le_right : K.U i ⊓ K.U j ≤ K.U j) (conormalCechVertexSection F K c.val j) := by
  have ordered (i j : K.ι) (hij : i < j) (W : X.Opens)
      (hi : W ≤ K.U i) (hj : W ≤ K.U j) :
      F.res hi (conormalCechVertexSection F K c.val i) =
      F.res hj (conormalCechVertexSection F K c.val j) := by
    let s : K.Idx 1 := ⟨![i, j], by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all⟩
    have hface0 : K.face s 0 = conormalCechVertex K j := by
      apply Subtype.ext
      funext a
      fin_cases a
      rfl
    have hface1 : K.face s 1 = conormalCechVertex K i := by
      apply Subtype.ext
      funext a
      fin_cases a
      rfl
    have hs : W ≤ K.inter s := by
      apply le_iInf
      intro a
      fin_cases a
      · exact hi
      · exact hj
    have hc := congrFun c.property s
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two] at hc
    simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_one_zsmul,
      Pi.zero_apply] at hc
    have heq := eq_neg_of_add_eq_zero_left hc
    simp only [neg_neg] at heq
    have hc' := congrArg (F.res hs) heq
    simp only [OModulePresheaf.res_res] at hc'
    unfold conormalCechVertexSection
    simp only [OModulePresheaf.res_res]
    have ht (u v : K.Idx 0) (h : u = v)
        (hu : W ≤ K.inter u) (hv : W ≤ K.inter v) :
        F.res hu (c.val u) = F.res hv (c.val v) := by
      subst v
      rfl
    exact (ht _ _ hface1.symm _ _).trans
      (hc'.symm.trans (ht _ _ hface0 _ _))
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ordered i j hij _ inf_le_left inf_le_right
  · rfl
  · exact (ordered j i hji _ inf_le_right inf_le_left).symm

end HodgeLean.Foundations.Program.G32Native

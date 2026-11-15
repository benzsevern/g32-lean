import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-! Ordered simplicial models for finite collections of faces.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite
open scoped Simplicial
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

def faceComplex {n : ℕ} (P : PreAbstractSimplicialComplex (Fin (n + 1))) :
    (Δ[n] : SSet.{0}).Subcomplex :=
  ⨆ s : P.faces, SSet.stdSimplex.face s.val

theorem faceComplex_nondegenerate_mem {n j : ℕ}
    (P : PreAbstractSimplicialComplex (Fin (n + 1)))
    (x : (Δ[n] : SSet.{0}).nonDegenerate j) :
    x.val ∈ (faceComplex P).obj (op ⦋j⦌) ↔
      (SSet.stdSimplex.nonDegenerateEquiv' x).val ∈ P.faces := by
  change x.val ∈ (⨆ s : P.faces, SSet.stdSimplex.face s.val).obj _ ↔ _
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩
    apply (P.isRelLowerSet_faces s.property).2
    · intro a ha
      obtain ⟨i, rfl⟩ := (SSet.stdSimplex.nonDegenerateEquiv'_iff x a).mp ha
      exact (SSet.stdSimplex.mem_face_iff _ _).mp hs i
    · apply Finset.card_pos.mp
      rw [(SSet.stdSimplex.nonDegenerateEquiv' x).property]
      exact Nat.succ_pos _
  · intro hx
    refine ⟨⟨_, hx⟩, ?_⟩
    apply (SSet.stdSimplex.mem_face_iff _ _).mpr
    intro i
    exact (SSet.stdSimplex.nonDegenerateEquiv'_iff x _).mpr ⟨i, rfl⟩

def faceComplex_nondegenerateEquiv {n : ℕ}
    (P : PreAbstractSimplicialComplex (Fin (n + 1))) (j : ℕ) :
    (faceComplex P : SSet.{0}).nonDegenerate j ≃
      {s : Finset (Fin (n + 1)) // s ∈ P.faces ∧ s.card = j + 1} where
  toFun x :=
    let y : (Δ[n] : SSet.{0}).nonDegenerate j :=
      ⟨x.val.val, ((faceComplex P).mem_nonDegenerate_iff x.val).mp x.property⟩
    ⟨(SSet.stdSimplex.nonDegenerateEquiv' y).val,
      (faceComplex_nondegenerate_mem P y).mp x.val.property,
      (SSet.stdSimplex.nonDegenerateEquiv' y).property⟩
  invFun s :=
    let y := SSet.stdSimplex.nonDegenerateEquiv'.{0}.symm ⟨s.val, s.property.2⟩
    let hy : y.val ∈ (faceComplex P).obj (op ⦋j⦌) :=
      (faceComplex_nondegenerate_mem P y).mpr (by
        simpa only [y, Equiv.apply_symm_apply] using s.property.1)
    ⟨⟨y.val, hy⟩, ((faceComplex P).mem_nonDegenerate_iff ⟨y.val, hy⟩).mpr y.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : (Δ[n] : SSet.{0}).nonDegenerate j => y.val)
      (SSet.stdSimplex.nonDegenerateEquiv'.symm_apply_apply
      (⟨x.val.val, ((faceComplex P).mem_nonDegenerate_iff x.val).mp x.property⟩ :
        (Δ[n] : SSet.{0}).nonDegenerate j))
  right_inv s := by
    apply Subtype.ext
    exact congrArg (fun y : {s : Finset (Fin (n + 1)) // s.card = j + 1} => y.val)
      (SSet.stdSimplex.nonDegenerateEquiv'.apply_symm_apply ⟨s.val, s.property.2⟩)

end HodgeLean.Foundations.IntegralHomology.StageTwo

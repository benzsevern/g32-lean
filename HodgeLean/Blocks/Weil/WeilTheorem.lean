import HodgeLean.Blocks.Weil.WedgeType
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # The top exterior line of a Weil eigenspace -/

open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 4000000

namespace HodgeBlocks

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

section LinearAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module.Finite ℂ E]

/-- Equal source subspaces give equal ranges after mapping an exterior power into the ambient
space.  Keeping the equality as a separate argument lets `subst` perform the dependent
transport before the surrounding range inclusion is elaborated. -/
theorem exteriorPower_map_subtype_range_eq_of_eq (n : ℕ) (P₀ P₁ : Submodule ℂ E)
    (h : P₀ = P₁) :
    LinearMap.range (exteriorPower.map n P₀.subtype) =
      LinearMap.range (exteriorPower.map n P₁.subtype) := by
  subst P₁
  rfl

/-- The top exterior power of a direct sum of two `k`-dimensional subspaces has wedge type
`(k,k)`.  The statement is made after mapping the top exterior power of the sum into `E`. -/
theorem topExteriorPower_sup_le_wedgeType (P Q : Submodule ℂ E)
    (hdis : P ⊓ Q = ⊥) (hdim : Module.finrank ℂ Q = Module.finrank ℂ P) :
    LinearMap.range
        (exteriorPower.map (Module.finrank ℂ P + Module.finrank ℂ P) (P ⊔ Q).subtype) ≤
      wedgeType P Q (Module.finrank ℂ P) (Module.finrank ℂ P) := by
  let k := Module.finrank ℂ P
  have hfin : Module.finrank ℂ ↥(P ⊔ Q) = k + k := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [hdis, finrank_bot, add_zero, hdim] at h
    omega
  change LinearMap.range (exteriorPower.map (k + k) (P ⊔ Q).subtype) ≤
    wedgeType P Q k k
  let f : ↥P × ↥Q →ₗ[ℂ] ↥(P ⊔ Q) :=
    { toFun := fun x => ⟨x.1.1 + x.2.1,
        Submodule.add_mem _ (Submodule.mem_sup_left x.1.2) (Submodule.mem_sup_right x.2.2)⟩
      map_add' := by intros; ext; simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]; abel
      map_smul' := by intros; ext; simp }
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨p, q⟩ ⟨p', q'⟩ heq
      have hsum : p.1 + q.1 = p'.1 + q'.1 := by
        have := congrArg Subtype.val heq
        simpa [f] using this
      have hpq : p.1 - p'.1 ∈ P ⊓ Q := ⟨P.sub_mem p.2 p'.2, by
        have heq : p.1 - p'.1 = -(q.1 - q'.1) := by
          apply eq_neg_of_add_eq_zero_left
          calc
            (p.1 - p'.1) + (q.1 - q'.1) = (p.1 + q.1) - (p'.1 + q'.1) := by abel
            _ = 0 := sub_eq_zero.mpr hsum
        rw [heq]
        exact Q.neg_mem (Q.sub_mem q.2 q'.2)⟩
      have hp0 : p.1 - p'.1 = 0 := by
        rw [hdis, Submodule.mem_bot] at hpq
        exact hpq
      have hp_eq : p = p' := Subtype.ext (sub_eq_zero.mp hp0)
      have hq_eq : q = q' := by
        apply Subtype.ext
        rw [hp_eq] at hsum
        exact add_left_cancel hsum
      simp [hp_eq, hq_eq]
    · rintro ⟨x, hx⟩
      rcases Submodule.mem_sup.mp hx with ⟨p, hp, q, hq, rfl⟩
      exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  let e : (↥P × ↥Q) ≃ₗ[ℂ] ↥(P ⊔ Q) := LinearEquiv.ofBijective f hf
  let bP : Module.Basis (Fin k) ℂ P := Module.finBasis ℂ P
  let bQ : Module.Basis (Fin k) ℂ Q :=
    (Module.finBasis ℂ Q).reindex (finCongr hdim)
  let b : Module.Basis (Fin (k + k)) ℂ ↥(P ⊔ Q) :=
    ((bP.prod bQ).map e).reindex finSumFinEquiv
  intro x hx
  rcases hx with ⟨y, rfl⟩
  let s : Set.powersetCard (Fin (k + k)) (k + k) :=
    ⟨Finset.univ, by simp⟩
  letI : Unique (Set.powersetCard (Fin (k + k)) (k + k)) :=
    { default := s
      uniq := fun t => Subtype.ext (Finset.eq_univ_of_card t.1 (by simp [t.2])) }
  have hs (i : Fin (k + k)) : Set.powersetCard.ofFinEmbEquiv.symm s i = i := by
    exact congrFun (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono.eq_id i
  let c := (b.exteriorPower (k + k)).repr y s
  have hy : y = c • b.exteriorPower (k + k) s := by
    symm
    simpa [c, show (default : Set.powersetCard (Fin (k + k)) (k + k)) = s from
      Subsingleton.elim _ _] using
      (b.exteriorPower (k + k)).sum_repr y
  rw [hy, map_smul]
  apply Submodule.smul_mem
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  have hm := DFunLike.congr_fun
    (exteriorPower.map_comp_ιMulti (P ⊔ Q).subtype)
    (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)
  have hm' : exteriorPower.map (k + k) (P ⊔ Q).subtype
      (exteriorPower.ιMulti ℂ (k + k)
        (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) =
      exteriorPower.ιMulti ℂ (k + k)
        ((P ⊔ Q).subtype ∘ b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := by
    simpa using hm
  rw [hm']
  have hargs :
      (P ⊔ Q).subtype ∘ b ∘ Set.powersetCard.ofFinEmbEquiv.symm s =
        Fin.append (fun i => (bP i : E)) (fun i => (bQ i : E)) := by
    funext i
    simp only [Function.comp_apply]
    rw [hs]
    generalize hj : finSumFinEquiv.symm i = j
    have hi : i = finSumFinEquiv j := by
      rw [← hj, finSumFinEquiv.apply_symm_apply]
    subst i
    rw [show b (finSumFinEquiv j) = ((bP.prod bQ).map e) j by simp [b]]
    cases j with
    | inl i => simp [e, f]
    | inr i =>
      rw [finSumFinEquiv_apply_right, Fin.append_right]
      simp [e, f]
  rw [hargs]
  exact ιMulti_append_mem_wedgeType P Q k k
    (fun i => (bP i : E)) (fun i => (bP i).2)
    (fun i => (bQ i : E)) (fun i => (bQ i).2)

end LinearAlgebra

namespace WeilAction

variable {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)

/-- The two Hodge summands of the distinguished eigenspace have equal dimension under the
Weil-type balance condition and the explicit weight-one exhaustion hypothesis. -/
theorem finrank_inf_H01_eq_inf_H10
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) :
    Module.finrank ℂ ↥(A.Vs ⊓ M.H (0, 1)) =
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) := by
  let P := A.Vs ⊓ M.H (1, 0)
  let Q := A.Vs ⊓ M.H (0, 1)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [A.inf_H10_H01_Vs, ← A.Vs_eq_sup hH] at hdim
  rw [finrank_bot, add_zero] at hdim
  dsimp [P, Q] at hdim
  dsimp [WeilAction.IsWeilType] at hWeil
  omega

/-- Every element of the top exterior power of the distinguished Weil eigenspace, after its
natural inclusion in the ambient complexification, has wedge type `(k,k)`, where `k` is the
dimension of its `(1,0)` part. -/
theorem top_wedge_Vs_mem_wedgeType
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) :
    LinearMap.range
        (exteriorPower.map
          (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
            Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
          (Submodule.subtype A.Vs)) ≤
      wedgeType (A.Vs ⊓ M.H (1, 0)) (A.Vs ⊓ M.H (0, 1))
        (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
        (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) := by
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  calc
    LinearMap.range (exteriorPower.map (k + k) A.Vs.subtype) =
        LinearMap.range (exteriorPower.map (k + k)
          ((A.Vs ⊓ M.H (1, 0)) ⊔ (A.Vs ⊓ M.H (0, 1))).subtype) :=
      exteriorPower_map_subtype_range_eq_of_eq _ _ _ (A.Vs_eq_sup hH)
    _ ≤ wedgeType (A.Vs ⊓ M.H (1, 0)) (A.Vs ⊓ M.H (0, 1)) k k :=
      topExteriorPower_sup_le_wedgeType _ _ A.inf_H10_H01_Vs
        (A.finrank_inf_H01_eq_inf_H10 hH hWeil)

end WeilAction
end HodgeBlocks

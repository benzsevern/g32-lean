import HodgeLean.Blocks.HodgeStructure.TensorProduct
import HodgeLean.Blocks.HodgeStructure.HodgeClass
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic

/-! # Exterior powers

The eventual construction sends a weight-`n` structure on `V` to a weight-`k*n` structure on
`⋀[ℚ]^k V`.  It will use Mathlib's `exteriorPower` quotient and `ExteriorAlgebra.ιMulti` to
transport the tensor-product bigrading to the alternating quotient.

**UPDATED status (hodge-LEAN8, 2026-09-24):** two `k`-fold tensor-power Hodge structures now
coexist in this file, deliberately NOT proved equal to each other (see
`QHodgeStructure.tensorPowerFlat`'s own docstring for why and for which one later work should
use): `QHodgeStructure.tensorPower` (hodge-LEAN7, by induction on `k`, nesting the binary
`QHodgeStructure.tensor`) and `QHodgeStructure.tensorPowerFlat` (hodge-LEAN8, built directly and
non-inductively from the flat, permutation-actable `tensorFinePiece` family via
`DirectSum.IsInternal.piTensor`/`.regroupFibers'` in `HodgeBlocks/Algebra/TensorInternal.lean`).

**FURTHER UPDATED status (hodge-LEAN11, 2026-09-24):** permutation invariance of
`tensorPowerFlat`'s own bidegree pieces (`QHodgeStructure.map_reindex_tensorPowerFlat`, full
equality, not just of a single fine piece), the alternatising endomorphism
(`tensorPowerAlt`/`tensorPowerAltC`, preserving each piece via
`QHodgeStructure.tensorPowerAltC_mapsTo`), and the graded kernel via
`DirectSum.IsInternal.ker_isInternal` (`QHodgeStructure.tensorPowerFlat_ker_isInternal`) are all
now proved, together with the exact kernel identification `tensorPowerAlt_ker : ker
(tensorPowerAlt V k) = ker (tensorPowerToExteriorPower V k)` and the first half of the ℚ↔ℂ bridge
(`tensorPowerAltC_ker_eq_range`).

**FURTHER UPDATED status (hodge-LEAN13, 2026-09-24):** the general "quotient of an internal
direct sum by a submodule split across its summands stays internal" lemma
(`DirectSum.IsInternal.quotientMap_isInternal`, `HodgeBlocks/Algebra/TensorInternal.lean`) and its
companion `DirectSum.IsInternal.ker_eq_iSup_inf` are proved, closing the gap hodge-LEAN11 left
open. Using them, the quotient decomposition, transport to the literal exterior power, and
conjugation symmetry are all established below, yielding the full four-field
`QHodgeStructure.exteriorPower {n} (M : QHodgeStructure n V) (k : ℕ) : QHodgeStructure (k * n)
(⋀[ℚ]^k V)`. Additionally, `QHodgeStructure.isHodgeClass_exteriorPower` proves a wedge of Hodge
classes is a Hodge class of the exterior-power structure, for an arbitrary finite family `v : Fin
k → V`. **Not attempted this run:** the exterior algebra on a weight-1 structure as a graded
family whose degree-`k` piece has weight `k` (job task 4, gated on the wedge theorem above and
left for a future run within this run's worker budget).
-/

noncomputable section
namespace HodgeBlocks

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- The Hodge structure of weight zero concentrated in bidegree `(0,0)`. -/
def QHodgeStructure.trivial : QHodgeStructure 0 ℚ where
  H pq := if pq = (0, 0) then ⊤ else ⊥
  supported pq h := by
    split_ifs with hpq
    · subst pq; simp at h
    · rfl
  isInternal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · intro i
      by_cases hi : i = (0, 0)
      · subst i
        simp
      · simp [hi]
    · apply top_unique
      exact le_iSup_of_le (0, 0) (by simp)
  conj_symm p q := by
    by_cases h : (p, q) = (0, 0)
    · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      change Submodule.map (sigmaQ ℚ) ⊤ = ⊤
      rw [Submodule.map_top]
      apply LinearMap.range_eq_top.2
      intro x
      exact ⟨sigmaQ ℚ x, sigmaQ_involutive ℚ x⟩
    · have hs : (q, p) ≠ (0, 0) := by
        intro hs
        apply h
        rcases Prod.mk.inj hs with ⟨hq, hp⟩
        exact Prod.ext hp hq
      simp [h, hs]

/-- The canonical equivalence adding one tensor factor to a tensor power. -/
def tensorPowerSuccEquiv (k : ℕ) :
    TensorProduct ℚ V (TensorPower ℚ k V) ≃ₗ[ℚ] (TensorPower ℚ (k + 1) V) :=
  LinearEquiv.rTensor (TensorPower ℚ k V)
      (PiTensorProduct.subsingletonEquiv (R := ℚ) (s := fun _ : Fin 1 => V) 0).symm ≪≫ₗ
    TensorPower.mulEquiv ≪≫ₗ
    TensorPower.cast ℚ V (Nat.add_comm 1 k)

/-- Scalar extension from `ℚ` to `ℂ` commutes with finite tensor powers. -/
def tensorPowerBaseChange :
    (k : ℕ) → (TensorProduct ℚ ℂ (TensorPower ℚ k V)) ≃ₗ[ℂ]
      TensorPower ℂ k (TensorProduct ℚ ℂ V)
  | 0 =>
      QHodgeStructure.complexificationCongr
          (V := TensorPower ℚ 0 V) (W := ℚ)
          (PiTensorProduct.isEmptyEquiv (R := ℚ) (s := fun _ : Fin 0 => V) (Fin 0)) ≪≫ₗ
        TensorProduct.AlgebraTensorModule.rid ℚ ℂ ℂ ≪≫ₗ
        (PiTensorProduct.isEmptyEquiv
          (R := ℂ) (s := fun _ : Fin 0 => TensorProduct ℚ ℂ V) (Fin 0)).symm
  | k + 1 =>
      QHodgeStructure.complexificationCongr
          (V := TensorPower ℚ (k + 1) V)
          (W := TensorProduct ℚ V (TensorPower ℚ k V))
          (tensorPowerSuccEquiv (V := V) k).symm ≪≫ₗ
        tensorBaseChange (V := V) (W := TensorPower ℚ k V) ≪≫ₗ
        TensorProduct.congr (LinearEquiv.refl ℂ (TensorProduct ℚ ℂ V))
          (tensorPowerBaseChange k) ≪≫ₗ
        LinearEquiv.rTensor (TensorPower ℂ k (TensorProduct ℚ ℂ V))
          (PiTensorProduct.subsingletonEquiv
            (R := ℂ) (s := fun _ : Fin 1 => TensorProduct ℚ ℂ V) 0).symm ≪≫ₗ
        TensorPower.mulEquiv ≪≫ₗ
        TensorPower.cast ℂ (TensorProduct ℚ ℂ V) (Nat.add_comm 1 k)

/-- The zero-fold scalar-extension comparison is the canonical composite through `ℚ` and `ℂ`. -/
theorem tensorPowerBaseChange_zero :
    tensorPowerBaseChange V 0 =
      (QHodgeStructure.complexificationCongr
          (V := TensorPower ℚ 0 V) (W := ℚ)
          (PiTensorProduct.isEmptyEquiv (R := ℚ) (s := fun _ : Fin 0 => V) (Fin 0)) ≪≫ₗ
        TensorProduct.AlgebraTensorModule.rid ℚ ℂ ℂ ≪≫ₗ
        (PiTensorProduct.isEmptyEquiv
          (R := ℂ) (s := fun _ : Fin 0 => TensorProduct ℚ ℂ V) (Fin 0)).symm) :=
  rfl

/-- Recursive compatibility of scalar extension with the chosen successor presentations of
tensor powers.  This is the commuting comparison used in the induction for Hodge pieces. -/
theorem tensorPowerBaseChange_succ (k : ℕ) :
    tensorPowerBaseChange V (k + 1) =
      (QHodgeStructure.complexificationCongr
          (V := TensorPower ℚ (k + 1) V)
          (W := TensorProduct ℚ V (TensorPower ℚ k V))
          (tensorPowerSuccEquiv (V := V) k).symm ≪≫ₗ
        tensorBaseChange (V := V) (W := TensorPower ℚ k V) ≪≫ₗ
        TensorProduct.congr (LinearEquiv.refl ℂ (TensorProduct ℚ ℂ V))
          (tensorPowerBaseChange V k) ≪≫ₗ
        LinearEquiv.rTensor (TensorPower ℂ k (TensorProduct ℚ ℂ V))
          (PiTensorProduct.subsingletonEquiv
            (R := ℂ) (s := fun _ : Fin 1 => TensorProduct ℚ ℂ V) 0).symm ≪≫ₗ
        TensorPower.mulEquiv ≪≫ₗ
        TensorPower.cast ℂ (TensorProduct ℚ ℂ V) (Nat.add_comm 1 k)) :=
  rfl

#print axioms tensorPowerBaseChange
#print axioms tensorPowerBaseChange_zero
#print axioms tensorPowerBaseChange_succ

variable [Module.Finite ℚ V]

/-- The tensor-product piece obtained by choosing one Hodge bidegree in each tensor factor.
This lives in the complex tensor power; relating it to the recursively constructed
`QHodgeStructure.tensorPower` requires the scalar-extension comparison map. -/
def QHodgeStructure.tensorFinePiece {n : ℤ} (M : QHodgeStructure n V) (k : ℕ)
    (p : Fin k → ℤ × ℤ) :
    Submodule ℂ (TensorPower ℂ k (TensorProduct ℚ ℂ V)) :=
  LinearMap.range (PiTensorProduct.map fun i => (M.H (p i)).subtype)

/-- Reindexing tensor factors maps a fine tensor piece into the correspondingly reindexed
fine piece.  The `e.symm` order agrees with `PiTensorProduct.reindex_tprod`.  Applying this
inclusion to `e.symm` gives the reverse inclusion when needed. -/
theorem QHodgeStructure.map_reindex_tensorFinePiece_le {n : ℤ} (M : QHodgeStructure n V)
    (k : ℕ) (p : Fin k → ℤ × ℤ) (e : Equiv.Perm (Fin k)) :
    (M.tensorFinePiece (V := V) k p).map
        (PiTensorProduct.reindex ℂ (fun _ : Fin k => TensorProduct ℚ ℂ V) e).toLinearMap ≤
      M.tensorFinePiece (V := V) k (p ∘ e.symm) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨PiTensorProduct.reindex ℂ (fun i : Fin k => M.H (p i)) e x, ?_⟩
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x => simp [Function.comp_def]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Reindexing tensor factors carries a fine piece exactly onto the permuted fine piece. -/
theorem QHodgeStructure.map_reindex_tensorFinePiece {n : ℤ} (M : QHodgeStructure n V)
    (k : ℕ) (p : Fin k → ℤ × ℤ) (e : Equiv.Perm (Fin k)) :
    (M.tensorFinePiece (V := V) k p).map
        (PiTensorProduct.reindex ℂ (fun _ : Fin k => TensorProduct ℚ ℂ V) e).toLinearMap =
      M.tensorFinePiece (V := V) k (p ∘ e.symm) := by
  apply le_antisymm
  · exact M.map_reindex_tensorFinePiece_le (V := V) k p e
  · have h := M.map_reindex_tensorFinePiece_le (V := V) k (p ∘ e.symm) e.symm
    simp only [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self,
      Function.comp_id] at h
    have h' :
        ((M.tensorFinePiece (V := V) k (p ∘ e.symm)).map
          (PiTensorProduct.reindex ℂ
            (fun _ : Fin k => TensorProduct ℚ ℂ V) e.symm).toLinearMap).map
          (PiTensorProduct.reindex ℂ
            (fun _ : Fin k => TensorProduct ℚ ℂ V) e).toLinearMap ≤
        (M.tensorFinePiece (V := V) k p).map
          (PiTensorProduct.reindex ℂ
            (fun _ : Fin k => TensorProduct ℚ ℂ V) e).toLinearMap :=
      Submodule.map_mono h
    rw [← Submodule.map_comp] at h'
    have hc :
        (PiTensorProduct.reindex ℂ
            (fun _ : Fin k => TensorProduct ℚ ℂ V) e).toLinearMap.comp
          (PiTensorProduct.reindex ℂ
            (fun _ : Fin k => TensorProduct ℚ ℂ V) e.symm).toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [hc, Submodule.map_id] at h'
    exact h'

/-- The two components of the total bidegree are unchanged by permuting tensor factors. -/
theorem tensorFinePiece_totalDegree_perm (k : ℕ) (p : Fin k → ℤ × ℤ)
    (e : Equiv.Perm (Fin k)) :
    (∑ i, ((p ∘ e.symm) i).1, ∑ i, ((p ∘ e.symm) i).2) =
      (∑ i, (p i).1, ∑ i, (p i).2) := by
  simp only [Function.comp_apply]
  apply Prod.ext
  · change (∑ i, (p (e.symm i)).1) = ∑ i, (p i).1
    exact Equiv.sum_comp e.symm (fun i => (p i).1)
  · change (∑ i, (p (e.symm i)).2) = ∑ i, (p i).2
    exact Equiv.sum_comp e.symm (fun i => (p i).2)

#print axioms QHodgeStructure.tensorFinePiece
#print axioms QHodgeStructure.map_reindex_tensorFinePiece_le
#print axioms QHodgeStructure.map_reindex_tensorFinePiece
#print axioms tensorFinePiece_totalDegree_perm

/-- The tensor-power Hodge structure, constructed inductively from the binary tensor product. -/
def QHodgeStructure.tensorPower {n : ℤ} (M : QHodgeStructure n V) :
    (k : ℕ) → QHodgeStructure (k * n) (TensorPower ℚ k V)
  | 0 => by
      simpa using QHodgeStructure.congr (V := ℚ) QHodgeStructure.trivial
        (PiTensorProduct.isEmptyEquiv (R := ℚ) (s := fun _ : Fin 0 => V) (Fin 0)).symm
  | k + 1 => by
      simpa [Nat.cast_add, add_mul, add_comm] using
        QHodgeStructure.congr (V := TensorProduct ℚ V (TensorPower ℚ k V))
          (QHodgeStructure.tensor M (M.tensorPower k))
          (tensorPowerSuccEquiv (V := V) k)

#print axioms QHodgeStructure.trivial
#print axioms tensorPowerSuccEquiv
#print axioms QHodgeStructure.tensorPower

/-- Pure wedges span the `k`th exterior power.  This is a direct restatement of Mathlib's own
`exteriorPower.ιMulti_span` (not new mathematical content), kept here as the surjectivity-on-
generators fact the eventual Hodge-structure quotient construction will need; Mathlib presents
`exteriorPower.ιMulti` as an alternating map rather than as a linear map out of a tensor power. -/
theorem exteriorPower_spanned_by_wedges (k : ℕ) :
    Submodule.span ℚ (Set.range (exteriorPower.ιMulti ℚ k (M := V))) =
      (⊤ : Submodule ℚ (⋀[ℚ]^k V)) :=
  exteriorPower.ιMulti_span ℚ k V

#print axioms exteriorPower_spanned_by_wedges

/-- The canonical linear map from the `Fin k`-indexed tensor power to Mathlib's literal
`k`th exterior power.  It is the tensor-product lift of the canonical alternating wedge map. -/
def tensorPowerToExteriorPower (k : ℕ) :
    TensorPower ℚ k V →ₗ[ℚ] (⋀[ℚ]^k V) :=
  PiTensorProduct.lift (exteriorPower.ιMulti ℚ k (M := V)).toMultilinearMap

@[simp] theorem tensorPowerToExteriorPower_tprod (k : ℕ) (v : Fin k → V) :
    tensorPowerToExteriorPower V k (PiTensorProduct.tprod ℚ v) =
      exteriorPower.ιMulti ℚ k v :=
  PiTensorProduct.lift.tprod v

/-- The canonical map from the indexed tensor power onto the literal exterior power is
surjective.  Thus Mathlib's exterior power is concretely the quotient by this map's kernel. -/
theorem tensorPowerToExteriorPower_surjective (k : ℕ) :
    Function.Surjective (tensorPowerToExteriorPower V k) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← exteriorPower.ιMulti_span ℚ k V]
  refine Submodule.span_le.2 ?_
  rintro x ⟨v, rfl⟩
  exact ⟨PiTensorProduct.tprod ℚ v, tensorPowerToExteriorPower_tprod V k v⟩

/-- The precise bridge between the tensor-power presentation and Mathlib's exterior-power
submodule: quotienting the tensor power by the kernel of the wedge map gives the latter. -/
def tensorPowerQuotientEquivExteriorPower (k : ℕ) :
    (TensorPower ℚ k V ⧸ LinearMap.ker (tensorPowerToExteriorPower V k)) ≃ₗ[ℚ]
      (⋀[ℚ]^k V) :=
  (tensorPowerToExteriorPower V k).quotKerEquivOfSurjective
    (tensorPowerToExteriorPower_surjective V k)

#print axioms tensorPowerToExteriorPower
#print axioms tensorPowerToExteriorPower_tprod
#print axioms tensorPowerToExteriorPower_surjective
#print axioms tensorPowerQuotientEquivExteriorPower

/-- The sum of the bidegrees selected in all factors of a tensor power. -/
def totalBidegree (k : ℕ) (p : Fin k → ℤ × ℤ) : ℤ × ℤ :=
  (∑ i, (p i).1, ∑ i, (p i).2)

/-- The flat fine-piece decomposition, regrouped by total bidegree, is internal. -/
theorem QHodgeStructure.tensorFinePiece_isInternal {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) :
    DirectSum.IsInternal (fun q : ℤ × ℤ =>
      ⨆ p ∈ (totalBidegree k) ⁻¹' {q}, M.tensorFinePiece (V := V) k p) := by
  classical
  have hfine : DirectSum.IsInternal (M.tensorFinePiece (V := V) k) := by
    change DirectSum.IsInternal (fun p : Fin k → ℤ × ℤ =>
      LinearMap.range (PiTensorProduct.map fun i => (M.H (p i)).subtype))
    exact DirectSum.IsInternal.piTensor (R := ℂ) (ι := Fin k)
      (M := fun _ => TensorProduct ℚ ℂ V)
      (κ := fun _ => ℤ × ℤ) (A := fun _ => M.H) (fun _ => M.isInternal)
  exact hfine.regroupFibers' (totalBidegree k)

#print axioms totalBidegree
#print axioms QHodgeStructure.tensorFinePiece_isInternal

/-- A fine tensor piece vanishes if one selected factor is outside the support of `M`. -/
theorem QHodgeStructure.tensorFinePiece_eq_bot_of_unsupported {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) (p : Fin k → ℤ × ℤ) (i : Fin k)
    (hi : (p i).1 + (p i).2 ≠ n) :
    M.tensorFinePiece (V := V) k p = ⊥ := by
  unfold QHodgeStructure.tensorFinePiece
  have hpiece : M.H (p i) = ⊥ := M.supported (p i) hi
  apply LinearMap.range_eq_bot.2
  apply LinearMap.ext
  intro z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      have hxi : x i = 0 := by
        apply Subtype.ext
        have hmem := (x i).property
        have hbot : (x i : TensorProduct ℚ ℂ V) ∈ (⊥ : Submodule ℂ _) :=
          hpiece ▸ hmem
        simpa using hbot
      calc
        (PiTensorProduct.map fun j => (M.H (p j)).subtype)
            (r • PiTensorProduct.tprod ℂ x) =
            r • PiTensorProduct.tprod ℂ (fun j => (x j : TensorProduct ℚ ℂ V)) := by
              rw [map_smul, PiTensorProduct.map_tprod]
              congr 2
        _ = 0 := by
          rw [(PiTensorProduct.tprod ℂ).map_coord_zero i (by simpa using hxi), smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- A total-bidegree fibre away from weight `k*n` consists of zero fine pieces. -/
theorem QHodgeStructure.tensorFinePiece_fiber_supported {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) (q : ℤ × ℤ)
    (h : q.1 + q.2 ≠ k * n) :
    (⨆ p ∈ (totalBidegree k) ⁻¹' {q}, M.tensorFinePiece (V := V) k p) = ⊥ := by
  classical
  apply iSup_eq_bot.2
  intro p
  apply iSup_eq_bot.2
  intro hp
  have hp' : totalBidegree k p = q := by simpa using hp
  have hbad : ∃ i, (p i).1 + (p i).2 ≠ n := by
    by_contra hall
    push_neg at hall
    apply h
    have hs : (∑ i, ((p i).1 + (p i).2)) = ∑ _i : Fin k, n :=
      Finset.sum_congr rfl fun i _ => hall i
    have hq1 := congrArg Prod.fst hp'
    have hq2 := congrArg Prod.snd hp'
    simp only [totalBidegree, Prod.fst, Prod.snd] at hq1 hq2
    rw [Finset.sum_add_distrib] at hs
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    omega
  obtain ⟨i, hi⟩ := hbad
  exact M.tensorFinePiece_eq_bot_of_unsupported (V := V) k p i hi

#print axioms QHodgeStructure.tensorFinePiece_eq_bot_of_unsupported
#print axioms QHodgeStructure.tensorFinePiece_fiber_supported

/-- Swap both components of every bidegree in a flat tensor index. -/
def swapAllBidegrees (k : ℕ) (p : Fin k → ℤ × ℤ) : Fin k → ℤ × ℤ :=
  fun i => ((p i).2, (p i).1)

@[simp] theorem totalBidegree_swapAllBidegrees (k : ℕ) (p : Fin k → ℤ × ℤ) :
    totalBidegree k (swapAllBidegrees k p) = (totalBidegree k p).swap := by
  rfl

/-- Factorwise rational conjugation on a complex tensor power. -/
def tensorPowerSigma (k : ℕ) :
    TensorPower ℂ k (TensorProduct ℚ ℂ V) →ₗ⋆[ℂ]
      TensorPower ℂ k (TensorProduct ℚ ℂ V) :=
  let F : TensorPower ℂ k (TensorProduct ℚ ℂ V) →+
      TensorPower ℂ k (TensorProduct ℚ ℂ V) :=
    PiTensorProduct.liftAddHom
      (fun rf => PiTensorProduct.tprodCoeff ℂ (star rf.1) (fun i => sigmaQ V (rf.2 i)))
      (fun r f i hi => by
        dsimp
        apply PiTensorProduct.zero_tprodCoeff' (star r) _ i
        simp [hi])
      (fun f => by simp [PiTensorProduct.zero_tprodCoeff])
      (fun r f i x y => by
        dsimp
        have hu (z : TensorProduct ℚ ℂ V) :
            (fun j => sigmaQ V (Function.update f i z j)) =
              Function.update (fun j => sigmaQ V (f j)) i (sigmaQ V z) := by
          funext j
          by_cases hji : j = i <;> simp [hji]
        rw [hu x, hu y, hu (x + y), map_add]
        exact PiTensorProduct.add_tprodCoeff (star r)
          (fun j => sigmaQ V (f j)) i (sigmaQ V x) (sigmaQ V y))
      (fun r r' f => by
        dsimp
        rw [map_add]
        exact PiTensorProduct.add_tprodCoeff' (star r) (star r')
          (fun i => sigmaQ V (f i)))
      (fun r f i r' => by
        dsimp
        rw [show (fun j => sigmaQ V (Function.update f i (r' • f i) j)) =
            Function.update (fun j => sigmaQ V (f j)) i (star r' • sigmaQ V (f i)) by
          funext j
          by_cases hji : j = i
          · subst j; simp
          · simp [hji]
          ]
        rw [PiTensorProduct.smul_tprodCoeff]
        congr 1
        simp only [smul_eq_mul]
        rw [map_mul]
        rfl)
  { toFun := F
    map_add' := F.map_add
    map_smul' := by
      intro c x
      induction x using PiTensorProduct.induction_on' with
      | tprodCoeff r f =>
          change PiTensorProduct.tprodCoeff ℂ (star (c * r))
              (fun i => sigmaQ V (f i)) =
            star c • PiTensorProduct.tprodCoeff ℂ (star r)
              (fun i => sigmaQ V (f i))
          rw [PiTensorProduct.smul_tprodCoeff']
          simp [map_mul]
      | add x y hx hy => simp only [PiTensorProduct.smul_add, map_add, hx, hy] }

@[simp] theorem tensorPowerSigma_tprod (k : ℕ)
    (x : Fin k → TensorProduct ℚ ℂ V) :
    tensorPowerSigma V k (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (fun i => sigmaQ V (x i)) := by
  change PiTensorProduct.tprodCoeff ℂ (star 1) (fun i => sigmaQ V (x i)) =
    PiTensorProduct.tprodCoeff ℂ 1 (fun i => sigmaQ V (x i))
  congr 1
  exact map_one (starRingEnd ℂ)

theorem tensorPowerSigma_involutive (k : ℕ)
    (x : TensorPower ℂ k (TensorProduct ℚ ℂ V)) :
    tensorPowerSigma V k (tensorPowerSigma V k x) = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem QHodgeStructure.tensorPowerSigma_mem_tensorFinePiece {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) (p : Fin k → ℤ × ℤ)
    {x : TensorPower ℂ k (TensorProduct ℚ ℂ V)}
    (hx : x ∈ M.tensorFinePiece (V := V) k p) :
    tensorPowerSigma V k x ∈
      M.tensorFinePiece (V := V) k (swapAllBidegrees k p) := by
  rcases hx with ⟨z, rfl⟩
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      let y : ∀ i, M.H ((swapAllBidegrees k p) i) := fun i =>
        ⟨sigmaQ V (x i), by
          change sigmaQ V (x i) ∈ M.H ((p i).2, (p i).1)
          rw [← M.conj_symm (p i).1 (p i).2]
          exact Submodule.mem_map_of_mem (x i).property⟩
      refine ⟨(starRingEnd ℂ) r • PiTensorProduct.tprod ℂ y, ?_⟩
      simp [y]
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

theorem QHodgeStructure.map_tensorPowerSigma_tensorFinePiece {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) (p : Fin k → ℤ × ℤ) :
    (M.tensorFinePiece (V := V) k p).map (tensorPowerSigma V k) =
      M.tensorFinePiece (V := V) k (swapAllBidegrees k p) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact M.tensorPowerSigma_mem_tensorFinePiece (V := V) k p hx
  · intro x hx
    refine ⟨tensorPowerSigma V k x, ?_, tensorPowerSigma_involutive V k x⟩
    have hm := M.tensorPowerSigma_mem_tensorFinePiece (V := V) k
      (swapAllBidegrees k p) hx
    rw [show swapAllBidegrees k (swapAllBidegrees k p) = p by
      funext i
      rfl] at hm
    exact hm

@[simp] theorem tensorPowerSuccEquiv_symm_tprod (k : ℕ) (v : Fin (k + 1) → V) :
    (tensorPowerSuccEquiv (V := V) k).symm (PiTensorProduct.tprod ℚ v) =
      v 0 ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ (fun i : Fin k => v i.succ) := by
  apply (tensorPowerSuccEquiv (V := V) k).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [tensorPowerSuccEquiv, LinearEquiv.trans_apply,
    LinearEquiv.rTensor_tmul, PiTensorProduct.subsingletonEquiv_symm_apply']
  rw [← TensorPower.gMul_def, TensorPower.tprod_mul_tprod, TensorPower.cast_tprod]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.append, Fin.addCases, Fin.cast]
  · simp [Fin.append, Fin.addCases, Fin.cast, Function.update]

@[simp] theorem tensorPowerBaseChange_tmul_tprod (k : ℕ) (c : ℂ) (v : Fin k → V) :
    tensorPowerBaseChange V k (c ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v) =
      PiTensorProduct.tprodCoeff ℂ c (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i) := by
  induction k with
  | zero =>
      simp [tensorPowerBaseChange, QHodgeStructure.complexificationCongr,
        PiTensorProduct.isEmptyEquiv]
      congr 2
      funext i
      exact Fin.elim0 i
  | succ k ih =>
      rw [tensorPowerBaseChange_succ]
      simp [tensorPowerSuccEquiv_symm_tprod, ih]
      rw [← TensorPower.gMul_def, TensorPower.tprod_mul_tprod, TensorPower.cast_tprod]
      congr 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Fin.append, Fin.addCases, Fin.cast, Function.update]
      · simp [Fin.append, Fin.addCases, Fin.cast, Function.update]

/-- Scalar extension of a rational tensor power intertwines rational conjugation with
factorwise conjugation on the complex tensor power. -/
theorem tensorPowerBaseChange_sigmaQR (k : ℕ)
    (x : TensorProduct ℚ ℂ (TensorPower ℚ k V)) :
    tensorPowerBaseChange V k (sigmaQR (TensorPower ℚ k V) x) =
      tensorPowerSigma V k (tensorPowerBaseChange V k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c z =>
      induction z using PiTensorProduct.induction_on generalizing c with
      | smul_tprod r v =>
          simp
          change tensorPowerBaseChange V k
              (((r : ℂ) * star c) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v) =
            tensorPowerSigma V k (tensorPowerBaseChange V k
              (((r : ℂ) * c) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v))
          rw [tensorPowerBaseChange_tmul_tprod, tensorPowerBaseChange_tmul_tprod]
          change PiTensorProduct.tprodCoeff ℂ ((r : ℂ) * star c)
              (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i) = _
          change _ = PiTensorProduct.tprodCoeff ℂ (star ((r : ℂ) * c))
            (fun i => sigmaQ V ((1 : ℂ) ⊗ₜ[ℚ] v i))
          congr 2
          · simp
          · funext i
            simp [sigmaQ, sigmaQR]
      | add x y hx hy =>
          rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add, map_add]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigma_tensorPowerBaseChange_symm (k : ℕ)
    (y : TensorPower ℂ k (TensorProduct ℚ ℂ V)) :
    sigmaQ (TensorPower ℚ k V) ((tensorPowerBaseChange V k).symm y) =
      (tensorPowerBaseChange V k).symm (tensorPowerSigma V k y) := by
  apply (tensorPowerBaseChange V k).injective
  change tensorPowerBaseChange V k (sigmaQR (TensorPower ℚ k V) _) = _
  rw [tensorPowerBaseChange_sigmaQR, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

theorem map_sigma_tensorPowerBaseChange_symm (k : ℕ)
    (P : Submodule ℂ (TensorPower ℂ k (TensorProduct ℚ ℂ V))) :
    (P.map (tensorPowerBaseChange V k).symm.toLinearMap).map
        (sigmaQ (TensorPower ℚ k V)) =
      (P.map (tensorPowerSigma V k)).map
        (tensorPowerBaseChange V k).symm.toLinearMap := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨tensorPowerSigma V k y, Submodule.mem_map_of_mem hy,
      (sigma_tensorPowerBaseChange_symm V k y).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨(tensorPowerBaseChange V k).symm y, ⟨y, hy, rfl⟩,
      sigma_tensorPowerBaseChange_symm V k y⟩

theorem QHodgeStructure.map_tensorPowerSigma_fiber {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) (p q : ℤ) :
    (⨆ a ∈ (totalBidegree k) ⁻¹' {(p, q)},
      M.tensorFinePiece (V := V) k a).map (tensorPowerSigma V k) =
      ⨆ a ∈ (totalBidegree k) ⁻¹' {(q, p)},
        M.tensorFinePiece (V := V) k a := by
  simp only [Submodule.map_iSup]
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun ha => ?_
    rw [M.map_tensorPowerSigma_tensorFinePiece (V := V) k a]
    refine le_iSup_of_le (swapAllBidegrees k a) (le_iSup_of_le ?_ le_rfl)
    simpa only [Set.mem_preimage, Set.mem_singleton_iff,
      totalBidegree_swapAllBidegrees, Prod.swap_prod_mk] using congrArg Prod.swap ha
  · refine iSup_le fun a => iSup_le fun ha => ?_
    refine le_iSup_of_le (swapAllBidegrees k a) (le_iSup_of_le ?_ ?_)
    · simpa only [Set.mem_preimage, Set.mem_singleton_iff,
        totalBidegree_swapAllBidegrees, Prod.swap_prod_mk] using congrArg Prod.swap ha
    · have h := (M.map_tensorPowerSigma_tensorFinePiece (V := V) k
        (swapAllBidegrees k a)).symm.le
      rw [show swapAllBidegrees k (swapAllBidegrees k a) = a by
        funext i
        rfl] at h
      exact h

/-- The flat tensor-power Hodge structure obtained by grouping fine pieces by total bidegree.

**hodge-LEAN8, 2026-09-24: NOT proved equal to `QHodgeStructure.tensorPower` above.** That
structure is built by induction on `k`, nesting the binary `QHodgeStructure.tensor`; this one is
built directly and non-inductively from the flat `tensorFinePiece` family, which is exactly what
permutation invariance (needed for the exterior-power quotient) requires a closed form for. Both
are genuine `QHodgeStructure (k * n) (TensorPower ℚ k V)` values on the same ambient module, and
they are expected to coincide, but **no agreement theorem between them has been proved or
attempted**. A future run building on permutation invariance / the exterior power should use
`tensorPowerFlat`, not `tensorPower`, and should either prove the two agree or retire
`tensorPower` once `tensorPowerFlat` is confirmed sufficient for every later step. -/
def QHodgeStructure.tensorPowerFlat {n : ℤ} (M : QHodgeStructure n V) (k : ℕ) :
    QHodgeStructure (k * n) (TensorPower ℚ k V) where
  H q := (⨆ p ∈ (totalBidegree k) ⁻¹' {q},
    M.tensorFinePiece (V := V) k p).map (tensorPowerBaseChange V k).symm.toLinearMap
  supported q h := by
    rw [M.tensorFinePiece_fiber_supported (V := V) k q h, Submodule.map_bot]
  isInternal := (M.tensorFinePiece_isInternal (V := V) k).mapEquiv
    (tensorPowerBaseChange V k).symm
  conj_symm p q := by
    rw [map_sigma_tensorPowerBaseChange_symm,
      M.map_tensorPowerSigma_fiber (V := V) k p q]

/-- Reindexing the factors of a rational tensor power by a permutation. -/
def reindexTensorPower (k : ℕ) (e : Equiv.Perm (Fin k)) :
    TensorPower ℚ k V ≃ₗ[ℚ] TensorPower ℚ k V :=
  PiTensorProduct.reindex ℚ (fun _ : Fin k => V) e

theorem tensorPowerBaseChange_reindex (k : ℕ) (e : Equiv.Perm (Fin k))
    (x : TensorProduct ℚ ℂ (TensorPower ℚ k V)) :
    tensorPowerBaseChange V k
        (QHodgeStructure.complexificationCongr
          (V := TensorPower ℚ k V) (W := TensorPower ℚ k V)
          (reindexTensorPower V k e) x) =
      (PiTensorProduct.reindex ℂ (fun _ : Fin k => TensorProduct ℚ ℂ V) e).toLinearMap
        (tensorPowerBaseChange V k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c z =>
      induction z using PiTensorProduct.induction_on generalizing c with
      | smul_tprod r v =>
          simp only [TensorProduct.tmul_smul]
          change tensorPowerBaseChange V k
              (QHodgeStructure.complexificationCongr
                (V := TensorPower ℚ k V) (W := TensorPower ℚ k V)
                (reindexTensorPower V k e)
                (((r : ℂ) * c) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v)) =
            (PiTensorProduct.reindex ℂ
              (fun _ : Fin k => TensorProduct ℚ ℂ V) e).toLinearMap
              (tensorPowerBaseChange V k
                (((r : ℂ) * c) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v))
          rw [QHodgeStructure.complexificationCongr_tmul]
          simp [reindexTensorPower, tensorPowerBaseChange_tmul_tprod,
            PiTensorProduct.tprodCoeff_eq_smul_tprod, Function.comp_def]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem QHodgeStructure.map_reindex_tensorFinePiece_fiber {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) (q : ℤ × ℤ) (e : Equiv.Perm (Fin k)) :
    (⨆ p ∈ (totalBidegree k) ⁻¹' {q}, M.tensorFinePiece (V := V) k p).map
        (PiTensorProduct.reindex ℂ (fun _ : Fin k => TensorProduct ℚ ℂ V) e).toLinearMap =
      ⨆ p ∈ (totalBidegree k) ⁻¹' {q}, M.tensorFinePiece (V := V) k p := by
  simp only [Submodule.map_iSup]
  apply le_antisymm
  · refine iSup_le fun p => iSup_le fun hp => ?_
    rw [M.map_reindex_tensorFinePiece (V := V) k p e]
    refine le_iSup_of_le (p ∘ e.symm) (le_iSup_of_le ?_ le_rfl)
    have ht := tensorFinePiece_totalDegree_perm k p e
    change totalBidegree k (p ∘ e.symm) = totalBidegree k p at ht
    change totalBidegree k (p ∘ e.symm) = q
    rw [ht]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hp
  · refine iSup_le fun p => iSup_le fun hp => ?_
    refine le_iSup_of_le (p ∘ e) (le_iSup_of_le ?_ ?_)
    · have ht := tensorFinePiece_totalDegree_perm k p e.symm
      change totalBidegree k (p ∘ e.symm.symm) = totalBidegree k p at ht
      change totalBidegree k (p ∘ e) = q
      rw [show totalBidegree k (p ∘ e) = totalBidegree k p by
        simpa only [Equiv.symm_symm] using ht]
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hp
    · have h := (M.map_reindex_tensorFinePiece (V := V) k (p ∘ e) e).symm.le
      simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using h

theorem map_reindex_tensorPowerBaseChange_symm (k : ℕ) (e : Equiv.Perm (Fin k))
    (P : Submodule ℂ (TensorPower ℂ k (TensorProduct ℚ ℂ V))) :
    (P.map (tensorPowerBaseChange V k).symm.toLinearMap).map
        (QHodgeStructure.complexificationCongr
          (V := TensorPower ℚ k V) (W := TensorPower ℚ k V)
          (reindexTensorPower V k e)).toLinearMap =
      (P.map (PiTensorProduct.reindex ℂ
        (fun _ : Fin k => TensorProduct ℚ ℂ V) e).toLinearMap).map
        (tensorPowerBaseChange V k).symm.toLinearMap := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(PiTensorProduct.reindex ℂ
      (fun _ : Fin k => TensorProduct ℚ ℂ V) e) y,
      Submodule.mem_map_of_mem hy, ?_⟩
    have h := congrArg (tensorPowerBaseChange V k).symm
      (tensorPowerBaseChange_reindex V k e
        ((tensorPowerBaseChange V k).symm y))
    simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] at h
    change (tensorPowerBaseChange V k).symm
        (PiTensorProduct.reindex ℂ
          (fun _ : Fin k => TensorProduct ℚ ℂ V) e y) =
      QHodgeStructure.complexificationCongr
        (V := TensorPower ℚ k V) (W := TensorPower ℚ k V)
        (reindexTensorPower V k e) ((tensorPowerBaseChange V k).symm y)
    exact h.symm
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(tensorPowerBaseChange V k).symm y, ⟨y, hy, rfl⟩, ?_⟩
    have h := congrArg (tensorPowerBaseChange V k).symm
      (tensorPowerBaseChange_reindex V k e
        ((tensorPowerBaseChange V k).symm y))
    simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] at h
    change QHodgeStructure.complexificationCongr
        (V := TensorPower ℚ k V) (W := TensorPower ℚ k V)
        (reindexTensorPower V k e) ((tensorPowerBaseChange V k).symm y) =
      (tensorPowerBaseChange V k).symm
        (PiTensorProduct.reindex ℂ
          (fun _ : Fin k => TensorProduct ℚ ℂ V) e y)
    exact h

theorem QHodgeStructure.map_reindex_tensorPowerFlat {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) (q : ℤ × ℤ) (e : Equiv.Perm (Fin k)) :
    ((M.tensorPowerFlat (V := V) k).H q).map
        (QHodgeStructure.complexificationCongr
          (V := TensorPower ℚ k V) (W := TensorPower ℚ k V)
          (reindexTensorPower V k e)).toLinearMap =
      (M.tensorPowerFlat (V := V) k).H q := by
  change
    (((⨆ p ∈ (totalBidegree k) ⁻¹' {q}, M.tensorFinePiece (V := V) k p).map
      (tensorPowerBaseChange V k).symm.toLinearMap).map
        (QHodgeStructure.complexificationCongr
          (V := TensorPower ℚ k V) (W := TensorPower ℚ k V)
          (reindexTensorPower V k e)).toLinearMap) = _
  rw [map_reindex_tensorPowerBaseChange_symm,
    M.map_reindex_tensorFinePiece_fiber (V := V) k q e]
  rfl

#print axioms tensorPowerSigma
#print axioms tensorPowerSigma_involutive
#print axioms QHodgeStructure.map_tensorPowerSigma_tensorFinePiece
#print axioms tensorPowerBaseChange_sigmaQR
#print axioms QHodgeStructure.tensorPowerFlat
#print axioms reindexTensorPower
#print axioms tensorPowerBaseChange_reindex
#print axioms QHodgeStructure.map_reindex_tensorFinePiece_fiber
#print axioms QHodgeStructure.map_reindex_tensorPowerFlat

/-- The alternatization operator on a tensor power: on pure tensors it is the signed sum over
all permutations of the tensor factors. -/
def tensorPowerAlt (k : ℕ) :
    TensorPower ℚ k V →ₗ[ℚ] TensorPower ℚ k V :=
  PiTensorProduct.lift
    (MultilinearMap.alternatization
      (PiTensorProduct.tprod ℚ :
        MultilinearMap ℚ (fun _ : Fin k => V) (TensorPower ℚ k V))).toMultilinearMap

@[simp] theorem tensorPowerAlt_tprod (k : ℕ) (v : Fin k → V) :
    tensorPowerAlt V k (PiTensorProduct.tprod ℚ v) =
      MultilinearMap.alternatization
        (PiTensorProduct.tprod ℚ :
          MultilinearMap ℚ (fun _ : Fin k => V) (TensorPower ℚ k V)) v :=
  PiTensorProduct.lift.tprod v

/-- The alternatization operator kills exactly the tensors killed by the canonical wedge map. -/
theorem tensorPowerAlt_ker (k : ℕ) :
    LinearMap.ker (tensorPowerAlt V k) =
      LinearMap.ker (tensorPowerToExteriorPower V k) := by
  classical
  let wedge := tensorPowerToExteriorPower V k
  let w : V [⋀^Fin k]→ₗ[ℚ] (⋀[ℚ]^k V) := exteriorPower.ιMulti ℚ k (M := V)
  let tprod : MultilinearMap ℚ (fun _ : Fin k => V) (TensorPower ℚ k V) :=
    PiTensorProduct.tprod ℚ
  let alt := MultilinearMap.alternatization tprod
  have hwedge : wedge.compMultilinearMap tprod = w.toMultilinearMap := by
    apply MultilinearMap.ext
    intro v
    simp [wedge, w, tprod]
  have hscaled : wedge.comp (tensorPowerAlt V k) = (Nat.factorial k : ℚ) • wedge := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    have h := LinearMap.compMultilinearMap_alternatization wedge tprod
    rw [hwedge, AlternatingMap.coe_alternatization] at h
    have hv := DFunLike.congr_fun h v
    simpa [wedge, w, tprod, alt, LinearMap.comp_apply,
      ← Nat.cast_smul_eq_nsmul ℚ] using hv.symm
  let s : (⋀[ℚ]^k V) →ₗ[ℚ] TensorPower ℚ k V :=
    exteriorPower.alternatingMapLinearEquiv alt
  have hfactor : s.comp wedge = tensorPowerAlt V k := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    have h := exteriorPower.alternatingMapLinearEquiv_comp_ιMulti alt
    have hv := DFunLike.congr_fun h v
    simpa [s, wedge, w, tprod, alt, LinearMap.comp_apply] using hv
  apply le_antisymm
  · intro x hx
    change tensorPowerAlt V k x = 0 at hx
    change tensorPowerToExteriorPower V k x = 0
    have hzero := congrArg (fun f : TensorPower ℚ k V →ₗ[ℚ] (⋀[ℚ]^k V) => f x) hscaled
    have hfac : (Nat.factorial k : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hs : (Nat.factorial k : ℚ) • tensorPowerToExteriorPower V k x = 0 := by
      simpa [wedge, LinearMap.comp_apply, hx] using hzero.symm
    exact (smul_eq_zero.mp hs).resolve_left hfac
  · intro x hx
    change tensorPowerToExteriorPower V k x = 0 at hx
    change tensorPowerAlt V k x = 0
    have heval := congrArg (fun f : TensorPower ℚ k V →ₗ[ℚ] TensorPower ℚ k V => f x) hfactor
    simpa [s, wedge, LinearMap.comp_apply, hx] using heval.symm

#print axioms tensorPowerAlt
#print axioms tensorPowerAlt_tprod
#print axioms tensorPowerAlt_ker

/-- The alternatization endomorphism is the signed sum of all tensor-factor reindexings. -/
theorem tensorPowerAlt_eq_sum_reindex (k : ℕ) :
    tensorPowerAlt V k =
      ∑ e : Equiv.Perm (Fin k),
        (Equiv.Perm.sign e : ℚ) • (reindexTensorPower V k e).toLinearMap := by
  classical
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change tensorPowerAlt V k (PiTensorProduct.tprod ℚ v) =
    (∑ e : Equiv.Perm (Fin k),
      (Equiv.Perm.sign e : ℚ) • (reindexTensorPower V k e).toLinearMap)
        (PiTensorProduct.tprod ℚ v)
  rw [tensorPowerAlt_tprod, MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearEquiv.coe_coe]
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin k)))]
  simp [reindexTensorPower, Equiv.inv_apply, Equiv.Perm.sign_inv]
  apply Finset.sum_congr rfl
  intro e _
  congr 2

#print axioms tensorPowerAlt_eq_sum_reindex

/-- Scalar extension of the tensor-power alternatization operator to `ℂ`. -/
def tensorPowerAltC (k : ℕ) :
    TensorProduct ℚ ℂ (TensorPower ℚ k V) →ₗ[ℂ]
      TensorProduct ℚ ℂ (TensorPower ℚ k V) :=
  (tensorPowerAlt V k).baseChange ℂ

/-- The kernel of complexified alternatization is the scalar extension of the rational
kernel, expressed as the range of its tensor-extended inclusion. -/
theorem tensorPowerAltC_ker_eq_range (k : ℕ) :
    LinearMap.ker (tensorPowerAltC V k) =
      LinearMap.range
        ((LinearMap.ker (tensorPowerAlt V k)).subtype.baseChange ℂ) := by
  have hexact := LinearMap.exact_subtype_ker_map (tensorPowerAlt V k)
  have hbase := Module.Flat.lTensor_exact (M := ℂ) hexact
  have hker := hbase.linearMap_ker_eq
  ext x
  change tensorPowerAltC V k x = 0 ↔ _
  have halt : tensorPowerAltC V k x = (tensorPowerAlt V k).lTensor ℂ x := by
    exact congrFun
      (LinearMap.baseChange_eq_ltensor (A := ℂ) (tensorPowerAlt V k)) x
  rw [halt]
  rw [LinearMap.mem_range]
  change (tensorPowerAlt V k).lTensor ℂ x = 0 ↔ ∃ y, _
  have hincl (y : TensorProduct ℚ ℂ (LinearMap.ker (tensorPowerAlt V k))) :
      (LinearMap.ker (tensorPowerAlt V k)).subtype.baseChange ℂ y =
        (LinearMap.ker (tensorPowerAlt V k)).subtype.lTensor ℂ y := by
    exact congrFun
      (LinearMap.baseChange_eq_ltensor
        (A := ℂ) (LinearMap.ker (tensorPowerAlt V k)).subtype) y
  constructor
  · intro hx
    have hxmem : x ∈ LinearMap.ker ((tensorPowerAlt V k).lTensor ℂ) := hx
    have hxrange : x ∈ LinearMap.range
        ((LinearMap.ker (tensorPowerAlt V k)).subtype.lTensor ℂ) := hker ▸ hxmem
    obtain ⟨y, hy⟩ := hxrange
    exact ⟨y, (hincl y).trans hy⟩
  · rintro ⟨y, hy⟩
    have hxrange : x ∈ LinearMap.range
        ((LinearMap.ker (tensorPowerAlt V k)).subtype.lTensor ℂ) :=
      ⟨y, (hincl y).symm.trans hy⟩
    have hxmem : x ∈ LinearMap.ker ((tensorPowerAlt V k).lTensor ℂ) := hker.symm ▸ hxrange
    exact hxmem

#print axioms tensorPowerAltC_ker_eq_range

/-- Base change of a rational tensor reindexing is its complexification. -/
theorem baseChange_reindexTensorPower (k : ℕ) (e : Equiv.Perm (Fin k)) :
    (reindexTensorPower V k e).toLinearMap.baseChange ℂ =
      (QHodgeStructure.complexificationCongr
        (V := TensorPower ℚ k V) (W := TensorPower ℚ k V)
        (reindexTensorPower V k e)).toLinearMap := by
  ext c
  simp

/-- Complexified alternatization is the signed sum of complexified reindexings. -/
theorem tensorPowerAltC_eq_sum_reindex (k : ℕ) :
    tensorPowerAltC V k =
      ∑ e : Equiv.Perm (Fin k), (Equiv.Perm.sign e : ℚ) •
        (QHodgeStructure.complexificationCongr
          (V := TensorPower ℚ k V) (W := TensorPower ℚ k V)
          (reindexTensorPower V k e)).toLinearMap := by
  classical
  unfold tensorPowerAltC
  rw [tensorPowerAlt_eq_sum_reindex]
  rw [show
    (∑ e : Equiv.Perm (Fin k),
      (Equiv.Perm.sign e : ℚ) • (reindexTensorPower V k e).toLinearMap).baseChange ℂ =
        ∑ e : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign e : ℚ) •
            (reindexTensorPower V k e).toLinearMap).baseChange ℂ by
      exact map_sum (LinearMap.baseChangeHom ℚ ℂ _ _) _ Finset.univ]
  apply Finset.sum_congr rfl
  intro e _
  rw [LinearMap.baseChange_smul, baseChange_reindexTensorPower]

/-- Complexified alternatization preserves every bidegree piece of the flat tensor-power
Hodge structure. -/
theorem QHodgeStructure.tensorPowerAltC_mapsTo {n : ℤ} (M : QHodgeStructure n V) (k : ℕ)
    (q : ℤ × ℤ) : ∀ x ∈ (M.tensorPowerFlat (V := V) k).H q,
      tensorPowerAltC V k x ∈ (M.tensorPowerFlat (V := V) k).H q := by
  classical
  intro x hx
  have he_mem (e : Equiv.Perm (Fin k)) :
      QHodgeStructure.complexificationCongr
          (V := TensorPower ℚ k V) (W := TensorPower ℚ k V)
          (reindexTensorPower V k e) x ∈
        (M.tensorPowerFlat (V := V) k).H q := by
    exact (le_of_eq (M.map_reindex_tensorPowerFlat (V := V) k q e))
      (Submodule.mem_map_of_mem hx)
  rw [tensorPowerAltC_eq_sum_reindex]
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro e _
  rw [LinearMap.smul_apply]
  change ((Equiv.Perm.sign e : ℚ) : ℂ) •
    QHodgeStructure.complexificationCongr
      (V := TensorPower ℚ k V) (W := TensorPower ℚ k V)
      (reindexTensorPower V k e) x ∈ (M.tensorPowerFlat (V := V) k).H q
  exact Submodule.smul_mem _ _ (he_mem e)

/-- The kernel of complexified alternatization inherits the flat tensor-power bigrading. -/
theorem QHodgeStructure.tensorPowerFlat_ker_isInternal {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) :
    DirectSum.IsInternal (fun q : ℤ × ℤ =>
      (((M.tensorPowerFlat (V := V) k).H q) ⊓
        LinearMap.ker (tensorPowerAltC V k)).submoduleOf
          (LinearMap.ker (tensorPowerAltC V k))) :=
  DirectSum.IsInternal.ker_isInternal (M.tensorPowerFlat (V := V) k).isInternal
    (tensorPowerAltC V k) (M.tensorPowerAltC_mapsTo (V := V) k)

#print axioms tensorPowerAltC
#print axioms baseChange_reindexTensorPower
#print axioms tensorPowerAltC_eq_sum_reindex
#print axioms QHodgeStructure.tensorPowerAltC_mapsTo
#print axioms QHodgeStructure.tensorPowerFlat_ker_isInternal

/-- The images of the flat tensor-power Hodge pieces form an internal decomposition after
quotienting by the kernel of complexified alternatization. -/
theorem QHodgeStructure.tensorPowerAltC_quot_isInternal {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) :
    DirectSum.IsInternal (fun q : ℤ × ℤ =>
      ((M.tensorPowerFlat (V := V) k).H q).map
        (LinearMap.ker (tensorPowerAltC V k)).mkQ) := by
  apply DirectSum.IsInternal.quotientMap_isInternal
    (M.tensorPowerFlat (V := V) k).isInternal
  exact DirectSum.IsInternal.ker_eq_iSup_inf
    (M.tensorPowerFlat (V := V) k).isInternal
    (tensorPowerAltC V k) (M.tensorPowerAltC_mapsTo (V := V) k)

#print axioms QHodgeStructure.tensorPowerAltC_quot_isInternal

/-- Base change preserves the standard description of a map's kernel as the range of the
base-changed kernel inclusion. -/
private theorem baseChange_ker_eq_range {X Y : Type*}
    [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
    (g : X →ₗ[ℚ] Y) :
    LinearMap.ker (g.baseChange ℂ) =
      LinearMap.range ((LinearMap.ker g).subtype.baseChange ℂ) := by
  have hexact := LinearMap.exact_subtype_ker_map g
  have hbase := Module.Flat.lTensor_exact (M := ℂ) hexact
  have hker := hbase.linearMap_ker_eq
  ext x
  change g.baseChange ℂ x = 0 ↔ _
  have hg : g.baseChange ℂ x = g.lTensor ℂ x := by
    exact congrFun (LinearMap.baseChange_eq_ltensor (A := ℂ) g) x
  rw [hg, LinearMap.mem_range]
  change g.lTensor ℂ x = 0 ↔ ∃ y, _
  have hincl (y : TensorProduct ℚ ℂ (LinearMap.ker g)) :
      (LinearMap.ker g).subtype.baseChange ℂ y =
        (LinearMap.ker g).subtype.lTensor ℂ y := by
    exact congrFun
      (LinearMap.baseChange_eq_ltensor (A := ℂ) (LinearMap.ker g).subtype) y
  constructor
  · intro hx
    have hxmem : x ∈ LinearMap.ker (g.lTensor ℂ) := hx
    have hxrange : x ∈ LinearMap.range ((LinearMap.ker g).subtype.lTensor ℂ) :=
      hker ▸ hxmem
    obtain ⟨y, hy⟩ := hxrange
    exact ⟨y, (hincl y).trans hy⟩
  · rintro ⟨y, hy⟩
    have hxrange : x ∈ LinearMap.range ((LinearMap.ker g).subtype.lTensor ℂ) :=
      ⟨y, (hincl y).symm.trans hy⟩
    have hxmem : x ∈ LinearMap.ker (g.lTensor ℂ) := hker.symm ▸ hxrange
    exact hxmem

/-- Complexified alternatization and the complexified wedge map have the same kernel. -/
theorem tensorPowerAltC_ker_eq_baseChange_wedge_ker (k : ℕ) :
    LinearMap.ker (tensorPowerAltC V k) =
      LinearMap.ker ((tensorPowerToExteriorPower V k).baseChange ℂ) := by
  rw [tensorPowerAltC_ker_eq_range, tensorPowerAlt_ker]
  exact (baseChange_ker_eq_range (tensorPowerToExteriorPower V k)).symm

/-- The quotient by complexified alternatization is canonically the complexification of the
exterior power. -/
noncomputable def QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (k : ℕ) :
    (TensorProduct ℚ ℂ (TensorPower ℚ k V) ⧸
        LinearMap.ker (tensorPowerAltC V k)) ≃ₗ[ℂ]
      TensorProduct ℚ ℂ (⋀[ℚ]^k V) :=
  Submodule.quotEquivOfEq _ _
      (tensorPowerAltC_ker_eq_baseChange_wedge_ker V k) ≪≫ₗ
    LinearMap.quotKerEquivOfSurjective
      ((tensorPowerToExteriorPower V k).baseChange ℂ)
      (LinearMap.baseChange_surjective ℂ
        (tensorPowerToExteriorPower_surjective V k))

@[simp] theorem QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC_mk (k : ℕ)
    (x : TensorProduct ℚ ℂ (TensorPower ℚ k V)) :
    QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (V := V) k
        (Submodule.Quotient.mk x) =
      (tensorPowerToExteriorPower V k).baseChange ℂ x := by
  simp [QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC]

#print axioms tensorPowerAltC_ker_eq_baseChange_wedge_ker
#print axioms QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC

/-- An internal family remains internal after transport by a linear equivalence. -/
private theorem isInternal_map_linearEquiv {R X Y I : Type*} [Field R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [DecidableEq I] (S : I → Submodule R X) (hS : DirectSum.IsInternal S)
    (e : X ≃ₗ[R] Y) :
    DirectSum.IsInternal (fun i => (S i).map e.toLinearMap) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hS ⊢
  constructor
  · have hm := hS.1.map_orderIso (Submodule.orderIsoMapComap e)
    simpa [Function.comp_def, Submodule.orderIsoMapComap_apply] using hm
  · rw [← Submodule.map_iSup, hS.2, Submodule.map_top, LinearEquiv.range]

/-- The intended exterior-power Hodge piece, obtained by quotienting the flat tensor-power
piece and transporting it to the complexified exterior power. -/
def QHodgeStructure.exteriorPowerH {n : ℤ} (M : QHodgeStructure n V) (k : ℕ)
    (q : ℤ × ℤ) : Submodule ℂ (TensorProduct ℚ ℂ (⋀[ℚ]^k V)) :=
  (((M.tensorPowerFlat (V := V) k).H q).map
      (LinearMap.ker (tensorPowerAltC V k)).mkQ).map
    (QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (V := V) k).toLinearMap

theorem QHodgeStructure.exteriorPowerH_supported {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) (q : ℤ × ℤ)
    (hq : q.1 + q.2 ≠ (k : ℤ) * n) :
    M.exteriorPowerH (V := V) k q = ⊥ := by
  rw [QHodgeStructure.exteriorPowerH,
    (M.tensorPowerFlat (V := V) k).supported q hq,
    Submodule.map_bot, Submodule.map_bot]

theorem QHodgeStructure.exteriorPowerH_isInternal {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) :
    DirectSum.IsInternal (M.exteriorPowerH (V := V) k) := by
  exact isInternal_map_linearEquiv _
    (M.tensorPowerAltC_quot_isInternal (V := V) k)
    (QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (V := V) k)

#print axioms QHodgeStructure.exteriorPowerH
#print axioms QHodgeStructure.exteriorPowerH_supported
#print axioms QHodgeStructure.exteriorPowerH_isInternal

/-- Scalar extension of a rational linear map commutes with rational conjugation. -/
theorem sigmaQ_baseChange {X Y : Type*} [AddCommGroup X] [Module ℚ X]
    [AddCommGroup Y] [Module ℚ Y] (g : X →ₗ[ℚ] Y)
    (x : TensorProduct ℚ ℂ X) :
    sigmaQ Y (g.baseChange ℂ x) = g.baseChange ℂ (sigmaQ X x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => simp [sigmaQ, sigmaQR]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Conjugation descends through the kernel of complexified alternatization. -/
noncomputable def sigmaQ_tensorPowerAltC_quot (k : ℕ) :
    (TensorProduct ℚ ℂ (TensorPower ℚ k V) ⧸ LinearMap.ker (tensorPowerAltC V k))
      →ₛₗ[starRingEnd ℂ]
    (TensorProduct ℚ ℂ (TensorPower ℚ k V) ⧸ LinearMap.ker (tensorPowerAltC V k)) := by
  let K := LinearMap.ker (tensorPowerAltC V k)
  apply Submodule.mapQ K K (sigmaQ (TensorPower ℚ k V))
  intro x hx
  change tensorPowerAltC V k (sigmaQ (TensorPower ℚ k V) x) = 0
  unfold tensorPowerAltC
  rw [← sigmaQ_baseChange (tensorPowerAlt V k)]
  change sigmaQ (TensorPower ℚ k V) (tensorPowerAltC V k x) = 0
  rw [show tensorPowerAltC V k x = 0 from hx]
  exact map_zero _

@[simp] theorem sigmaQ_tensorPowerAltC_quot_mk (k : ℕ)
    (x : TensorProduct ℚ ℂ (TensorPower ℚ k V)) :
    sigmaQ_tensorPowerAltC_quot V k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (sigmaQ (TensorPower ℚ k V) x) := by
  simp [sigmaQ_tensorPowerAltC_quot]

theorem sigmaQ_exteriorPowerC_quot_equiv (k : ℕ)
    (y : TensorProduct ℚ ℂ (TensorPower ℚ k V) ⧸
      LinearMap.ker (tensorPowerAltC V k)) :
    sigmaQ (⋀[ℚ]^k V)
        (QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (V := V) k y) =
      QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (V := V) k
        (sigmaQ_tensorPowerAltC_quot V k y) := by
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
      simp only [QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC_mk,
        sigmaQ_tensorPowerAltC_quot_mk]
      exact sigmaQ_baseChange (tensorPowerToExteriorPower V k) x

theorem QHodgeStructure.exteriorPowerH_conj_symm {n : ℤ}
    (M : QHodgeStructure n V) (k : ℕ) (p q : ℤ) :
    (M.exteriorPowerH (V := V) k (p, q)).map (sigmaQ (⋀[ℚ]^k V)) =
      M.exteriorPowerH (V := V) k (q, p) := by
  let K := LinearMap.ker (tensorPowerAltC V k)
  let e := QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (V := V) k
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨y, hy, rfl⟩
    rcases hy with ⟨x, hx, rfl⟩
    have hs : sigmaQ (TensorPower ℚ k V) x ∈
        (M.tensorPowerFlat (V := V) k).H (q, p) := by
      rw [← (M.tensorPowerFlat (V := V) k).conj_symm p q]
      exact Submodule.mem_map_of_mem hx
    refine ⟨K.mkQ (sigmaQ (TensorPower ℚ k V) x),
      ⟨_, hs, rfl⟩, ?_⟩
    dsimp [K]
    have h := sigmaQ_exteriorPowerC_quot_equiv V k
      ((LinearMap.ker (tensorPowerAltC V k)).mkQ x)
    have hm := sigmaQ_tensorPowerAltC_quot_mk V k x
    change sigmaQ (⋀[ℚ]^k V)
        (QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (V := V) k
          (Submodule.Quotient.mk x)) =
      QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (V := V) k
        (sigmaQ_tensorPowerAltC_quot V k (Submodule.Quotient.mk x)) at h
    rw [hm] at h
    exact h.symm
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨e (K.mkQ (sigmaQ (TensorPower ℚ k V) x)), ?_, ?_⟩
    · refine ⟨K.mkQ (sigmaQ (TensorPower ℚ k V) x), ?_, rfl⟩
      refine ⟨sigmaQ (TensorPower ℚ k V) x, ?_, rfl⟩
      rw [← (M.tensorPowerFlat (V := V) k).conj_symm q p]
      exact Submodule.mem_map_of_mem hx
    · rw [sigmaQ_exteriorPowerC_quot_equiv]
      simp

/-- Exterior powers of rational Hodge structures. -/
def QHodgeStructure.exteriorPower {n : ℤ} (M : QHodgeStructure n V) (k : ℕ) :
    QHodgeStructure (k * n) (⋀[ℚ]^k V) where
  H := M.exteriorPowerH (V := V) k
  supported := M.exteriorPowerH_supported (V := V) k
  isInternal := M.exteriorPowerH_isInternal (V := V) k
  conj_symm := M.exteriorPowerH_conj_symm (V := V) k

/-- Transport a Hodge structure along an equality of its weights. -/
private def QHodgeStructure.weightCast {n m : ℤ} (h : n = m)
    (M : QHodgeStructure n V) : QHodgeStructure m V :=
  h ▸ M

@[simp] private theorem QHodgeStructure.weightCast_H {n m : ℤ} (h : n = m)
    (M : QHodgeStructure n V) :
    (QHodgeStructure.weightCast (V := V) h M).H = M.H := by
  subst m
  rfl

/-- A wedge of Hodge classes is a Hodge class in the exterior-power Hodge structure. -/
theorem QHodgeStructure.isHodgeClass_exteriorPower {p : ℤ}
    (M : QHodgeStructure (2 * p) V) (k : ℕ) (v : Fin k → V)
    (hv : ∀ i, IsHodgeClass M (v i)) :
    IsHodgeClass (p := k * p)
      (QHodgeStructure.weightCast (V := ⋀[ℚ]^k V)
        (by ring)
        (M.exteriorPower (V := V) k))
      (exteriorPower.ιMulti ℚ k v) := by
  classical
  let K := LinearMap.ker (tensorPowerAltC V k)
  let e := QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (V := V) k
  let d : Fin k → ℤ × ℤ := fun _ => (p, p)
  have hd : d ∈ (totalBidegree k) ⁻¹' {(k * p, k * p)} := by
    change totalBidegree k d = (k * p, k * p)
    apply Prod.ext <;> simp [totalBidegree, d]
  have hfine :
      PiTensorProduct.tprod ℂ (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i) ∈
        M.tensorFinePiece (V := V) k d := by
    refine ⟨PiTensorProduct.tprod ℂ
      (fun i => (⟨(1 : ℂ) ⊗ₜ[ℚ] v i, hv i⟩ : M.H (d i))), ?_⟩
    rw [PiTensorProduct.map_tprod]
    rfl
  have hsum :
      PiTensorProduct.tprod ℂ (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i) ∈
        ⨆ d' ∈ (totalBidegree k) ⁻¹' {(k * p, k * p)},
          M.tensorFinePiece (V := V) k d' := by
    exact Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hd hfine)
  have hflat :
      (1 : ℂ) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v ∈
        (M.tensorPowerFlat (V := V) k).H (k * p, k * p) := by
    change (1 : ℂ) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v ∈
      (⨆ d' ∈ (totalBidegree k) ⁻¹' {(k * p, k * p)},
        M.tensorFinePiece (V := V) k d').map
          (tensorPowerBaseChange V k).symm.toLinearMap
    rw [Submodule.mem_map_equiv]
    simp only [LinearEquiv.symm_symm]
    rw [tensorPowerBaseChange_tmul_tprod]
    simpa using hsum
  have hquot : K.mkQ ((1 : ℂ) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v) ∈
      ((M.tensorPowerFlat (V := V) k).H (k * p, k * p)).map K.mkQ :=
    Submodule.mem_map_of_mem hflat
  have himage :
      e (K.mkQ ((1 : ℂ) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v)) =
        (1 : ℂ) ⊗ₜ[ℚ] exteriorPower.ιMulti ℚ k v := by
    dsimp [e, K]
    rw [QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC_mk]
    rw [LinearMap.baseChange_tmul]
    rw [tensorPowerToExteriorPower_tprod]
  have htarget :
      complexify (⋀[ℚ]^k V) (exteriorPower.ιMulti ℚ k v) ∈
        M.exteriorPowerH (V := V) k (k * p, k * p) := by
    rw [complexify_apply, QHodgeStructure.exteriorPowerH]
    rw [← himage]
    exact Submodule.mem_map_of_mem hquot
  simpa [IsHodgeClass, QHodgeStructure.exteriorPower] using htarget

#print axioms QHodgeStructure.weightCast_H
#print axioms QHodgeStructure.isHodgeClass_exteriorPower

#print axioms sigmaQ_baseChange
#print axioms sigmaQ_tensorPowerAltC_quot
#print axioms sigmaQ_tensorPowerAltC_quot_mk
#print axioms sigmaQ_exteriorPowerC_quot_equiv
#print axioms QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC_mk
#print axioms QHodgeStructure.exteriorPowerH_conj_symm
#print axioms QHodgeStructure.exteriorPower

end HodgeBlocks

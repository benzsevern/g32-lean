import HodgeLean.Blocks.Weil.Derivation
import HodgeLean.Blocks.Weil.WeilTheorem

/-! # The kernel of the Weil derivation polynomial

This file records the dimension calculations and the already-available inclusion at the
middle exterior degree.  They are the input to the reverse-inclusion argument.
-/

open scoped TensorProduct

noncomputable section

namespace HodgeBlocks
namespace WeilAction

/-- Under the Weil balance condition, the distinguished eigenspace has twice the dimension of
its `(1,0)` part. -/
theorem finrank_Vs_eq_twice_inf_H10 {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) :
    Module.finrank ℂ ↥A.Vs =
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
        Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) := by
  let P := A.Vs ⊓ M.H (1, 0)
  let Q := A.Vs ⊓ M.H (0, 1)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [A.inf_H10_H01_Vs, ← A.Vs_eq_sup hH, finrank_bot, add_zero] at hdim
  have hPQ : Module.finrank ℂ ↥Q = Module.finrank ℂ ↥P :=
    A.finrank_inf_H01_eq_inf_H10 hH hWeil
  dsimp [P, Q] at hdim hPQ ⊢
  omega

/-- The conjugate eigenspace has the same dimension as the distinguished eigenspace. -/
theorem finrank_Vsbar_eq_Vs {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d) :
    Module.finrank ℂ ↥A.Vsbar = Module.finrank ℂ ↥A.Vs := by
  rw [← A.map_Vs_sigmaQ]
  exact finrank_map_sigmaQ A.Vs

/-- The two top Weil eigenlines lie in the kernel at the middle exterior degree. -/
theorem eigenspace_sup_le_ker_middle {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)
    (hd : 0 < d) :
    let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
    LinearMap.range (exteriorPower.map (k + k) A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map (k + k) A.Vsbar.subtype) ≤
      LinearMap.ker (derivationKernelOperator A k) := by
  dsimp only
  exact A.sup_le_eigenspace_ker hd _

/-- A basis adapted to the two Weil eigenspaces, with its eigenvalue recorded pointwise. -/
theorem exists_adapted_Jc_basis {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)
    (hd : 0 < d) (n : ℕ) (hVs : Module.finrank ℂ ↥A.Vs = n)
    (hVsbar : Module.finrank ℂ ↥A.Vsbar = n) :
    ∃ b : Module.Basis (Fin (n + n)) ℂ (ℂ ⊗[ℚ] V), ∀ j,
      A.Jc (b j) =
        (if (finSumFinEquiv.symm j).isLeft then omegaC d else -omegaC d) • b j := by
  let e := Submodule.prodEquivOfIsCompl A.Vs A.Vsbar (isCompl_Vs_Vsbar A hd)
  let bVs : Module.Basis (Fin n) ℂ ↥A.Vs :=
    (Module.finBasis ℂ ↥A.Vs).reindex (finCongr hVs)
  let bVsbar : Module.Basis (Fin n) ℂ ↥A.Vsbar :=
    (Module.finBasis ℂ ↥A.Vsbar).reindex (finCongr hVsbar)
  let b0 := (bVs.prod bVsbar).map e
  let b := b0.reindex finSumFinEquiv
  refine ⟨b, ?_⟩
  intro j
  generalize hx : finSumFinEquiv.symm j = x
  have hj : j = finSumFinEquiv x := by
    rw [← hx, finSumFinEquiv.apply_symm_apply]
  subst j
  cases x with
  | inl i =>
      have hb : b (finSumFinEquiv (Sum.inl i)) = (bVs i : ℂ ⊗[ℚ] V) := by
        rw [show b (finSumFinEquiv (Sum.inl i)) = b0 (Sum.inl i) by simp [b]]
        rw [show b0 (Sum.inl i) = e (bVs i, 0) by simp [b0]]
        rw [Submodule.coe_prodEquivOfIsCompl']
        simp
      rw [hb]
      simpa using Module.End.mem_eigenspace_iff.mp (bVs i).2
  | inr i =>
      have hb : b (finSumFinEquiv (Sum.inr i)) = (bVsbar i : ℂ ⊗[ℚ] V) := by
        rw [show b (finSumFinEquiv (Sum.inr i)) = b0 (Sum.inr i) by
          rw [show b (finSumFinEquiv (Sum.inr i)) =
              b0 (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) by
            exact Module.Basis.reindex_apply b0 finSumFinEquiv _]
          exact congrArg b0 hx]
        rw [show b0 (Sum.inr i) = e (0, bVsbar i) by simp [b0]]
        rw [Submodule.coe_prodEquivOfIsCompl']
        simp
      rw [hb]
      simpa [finSumFinEquiv_apply_right] using
        Module.End.mem_eigenspace_iff.mp (bVsbar i).2

/-- A finite sum of two opposite scalars is determined by the number of positive signs. -/
private theorem sum_ite_eq_card_filter_sub (n : ℕ) (p : Fin n → Prop) [DecidablePred p]
    (z : ℂ) :
    (∑ i : Fin n, if p i then z else -z) =
      (2 * ((Finset.univ.filter p).card : ℂ) - (n : ℂ)) * z := by
  classical
  let L : Finset (Fin n) := Finset.univ.filter p
  have hcard : L.card + (Finset.univ.filter fun i : Fin n => ¬p i).card = n := by
    simpa [L] using Finset.card_filter_add_card_filter_not (s := Finset.univ) p
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p]
  rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_filter.mp hi).2),
    Finset.sum_congr rfl (fun i hi => if_neg (Finset.mem_filter.mp hi).2)]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcardC : (L.card : ℂ) +
      ((Finset.univ.filter fun i : Fin n => ¬p i).card : ℂ) = (n : ℂ) := by
    exact_mod_cast hcard
  dsimp [L] at hcard ⊢
  rw [show ((Finset.univ.filter fun i : Fin n => ¬p i).card : ℂ) =
      (n : ℂ) - ((Finset.univ.filter p).card : ℂ) by
        dsimp [L] at hcardC
        linear_combination hcardC]
  ring

/-- The exterior basis induced by an adapted basis diagonalizes the exterior derivation. -/
theorem derivationExt_adapted_exterior_basis
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d) (n : ℕ)
    (b : Module.Basis (Fin (n + n)) ℂ (ℂ ⊗[ℚ] V))
    (hb : ∀ j, A.Jc (b j) =
      (if (finSumFinEquiv.symm j).isLeft then omegaC d else -omegaC d) • b j)
    (s : Set.powersetCard (Fin (n + n)) n) :
    derivationExt A.Jc n (b.exteriorPower n s) =
      ((2 * ((Finset.univ.filter fun i : Fin n =>
          (finSumFinEquiv.symm (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft).card : ℂ) -
        (n : ℂ)) * omegaC d) • b.exteriorPower n s := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  rw [derivationExt_ιMulti_of_eigen A.Jc n _
    (fun i => if (finSumFinEquiv.symm
      (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft then omegaC d else -omegaC d)]
  · rw [sum_ite_eq_card_filter_sub]
  · intro i
    exact hb _

/-- The quadratic kernel operator is diagonal in an adapted exterior basis. -/
theorem derivationKernelOperator_adapted_exterior_basis
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d) (hd : 0 < d) (k : ℕ)
    (b : Module.Basis (Fin ((k + k) + (k + k))) ℂ (ℂ ⊗[ℚ] V))
    (hb : ∀ j, A.Jc (b j) =
      (if (finSumFinEquiv.symm j).isLeft then omegaC d else -omegaC d) • b j)
    (s : Set.powersetCard (Fin ((k + k) + (k + k))) (k + k)) :
    derivationKernelOperator A k (b.exteriorPower (k + k) s) =
      (4 * (((Finset.univ.filter fun i : Fin (k + k) =>
          (finSumFinEquiv.symm
            (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft).card : ℂ)) *
        ((k + k : ℕ) - (Finset.univ.filter fun i : Fin (k + k) =>
          (finSumFinEquiv.symm
            (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft).card) * (d : ℂ)) •
        b.exteriorPower (k + k) s := by
  classical
  let a := (Finset.univ.filter fun i : Fin (k + k) =>
    (finSumFinEquiv.symm (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft).card
  have ha : a ≤ k + k := by
    have hsub : (Finset.univ.filter fun i : Fin (k + k) =>
        (finSumFinEquiv.symm
          (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft) ⊆ Finset.univ :=
      Finset.filter_subset _ _
    simpa [a] using Finset.card_le_card hsub
  have hT := derivationExt_adapted_exterior_basis A (k + k) b hb s
  change derivationExt A.Jc (k + k)
      (derivationExt A.Jc (k + k) (b.exteriorPower (k + k) s)) +
      (4 * (k : ℂ) ^ 2 * (d : ℂ)) • b.exteriorPower (k + k) s = _
  rw [hT, map_smul, hT, smul_smul, ← add_smul]
  congr 1
  have hω : omegaC d ^ 2 = -(d : ℂ) := omegaC_sq hd
  calc
    _ = (2 * ((Finset.univ.filter fun i : Fin (k + k) =>
          (finSumFinEquiv.symm
            (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft).card : ℂ) -
          (k + k : ℂ)) ^ 2 * omegaC d ^ 2 +
        4 * (k : ℂ) ^ 2 * (d : ℂ) := by push_cast; ring
    _ = _ := by rw [hω]; push_cast; ring

/-- The kernel of the quadratic exterior derivation is exactly the sum of the two top Weil
eigenlines. -/
theorem ker_derivationKernelOperator_eq_sup {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) (hd : 0 < d) :
    LinearMap.ker
        (derivationKernelOperator A (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))) =
      LinearMap.range (exteriorPower.map
          (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
            Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map
          (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
            Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) A.Vsbar.subtype) := by
  classical
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  let n := k + k
  have hVs : Module.finrank ℂ ↥A.Vs = n := by
    simpa [k, n] using A.finrank_Vs_eq_twice_inf_H10 hH hWeil
  have hVsbar : Module.finrank ℂ ↥A.Vsbar = n := by
    rw [A.finrank_Vsbar_eq_Vs, hVs]
  obtain ⟨b, hb⟩ := A.exists_adapted_Jc_basis hd n hVs hVsbar
  let B := b.exteriorPower n
  let a : Set.powersetCard (Fin (n + n)) n → ℕ := fun s =>
    (Finset.univ.filter fun i : Fin n =>
      (finSumFinEquiv.symm
        (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft).card
  have ha_le (s : Set.powersetCard (Fin (n + n)) n) : a s ≤ n := by
    have hsub : (Finset.univ.filter fun i : Fin n =>
        (finSumFinEquiv.symm
          (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft) ⊆ Finset.univ :=
      Finset.filter_subset _ _
    simpa [a] using Finset.card_le_card hsub
  have hbasis_mem (s : Set.powersetCard (Fin (n + n)) n)
      (hs : a s = 0 ∨ a s = n) :
      B s ∈ LinearMap.range (exteriorPower.map n A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map n A.Vsbar.subtype) := by
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    rcases hs with hs | hs
    · have hempty : Finset.univ.filter (fun i : Fin n =>
          (finSumFinEquiv.symm
            (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft) = ∅ :=
        Finset.card_eq_zero.mp hs
      let v : Fin n → ↥A.Vsbar := fun i =>
        ⟨b (Set.powersetCard.ofFinEmbEquiv.symm s i), by
          apply Module.End.mem_eigenspace_iff.mpr
          have hi : ¬ (finSumFinEquiv.symm
              (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft := by
            intro hi
            have : i ∈ Finset.univ.filter (fun j : Fin n =>
                (finSumFinEquiv.symm
                  (Set.powersetCard.ofFinEmbEquiv.symm s j)).isLeft) := by simp [hi]
            simp [hempty] at this
          simpa [hi] using hb (Set.powersetCard.ofFinEmbEquiv.symm s i)⟩
      apply Submodule.mem_sup_right
      refine ⟨exteriorPower.ιMulti ℂ n v, ?_⟩
      rw [show exteriorPower.map n A.Vsbar.subtype (exteriorPower.ιMulti ℂ n v) =
          exteriorPower.ιMulti ℂ n (A.Vsbar.subtype ∘ v) by
        exact DFunLike.congr_fun (exteriorPower.map_comp_ιMulti A.Vsbar.subtype) v]
      rfl
    · have hall : Finset.univ.filter (fun i : Fin n =>
          (finSumFinEquiv.symm
            (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft) = Finset.univ :=
        Finset.eq_univ_of_card _ (by simpa using hs)
      let v : Fin n → ↥A.Vs := fun i =>
        ⟨b (Set.powersetCard.ofFinEmbEquiv.symm s i), by
          apply Module.End.mem_eigenspace_iff.mpr
          have hi : (finSumFinEquiv.symm
              (Set.powersetCard.ofFinEmbEquiv.symm s i)).isLeft := by
            have : i ∈ Finset.univ.filter (fun j : Fin n =>
                (finSumFinEquiv.symm
                  (Set.powersetCard.ofFinEmbEquiv.symm s j)).isLeft) := by
              simp [hall]
            exact (Finset.mem_filter.mp this).2
          simpa [hi] using hb (Set.powersetCard.ofFinEmbEquiv.symm s i)⟩
      apply Submodule.mem_sup_left
      refine ⟨exteriorPower.ιMulti ℂ n v, ?_⟩
      rw [show exteriorPower.map n A.Vs.subtype (exteriorPower.ιMulti ℂ n v) =
          exteriorPower.ιMulti ℂ n (A.Vs.subtype ∘ v) by
        exact DFunLike.congr_fun (exteriorPower.map_comp_ιMulti A.Vs.subtype) v]
      rfl
  apply le_antisymm
  · intro y hy
    rw [show y = ∑ s, B.repr y s • B s by
      symm
      simpa [B] using B.sum_repr y]
    apply Submodule.sum_mem
    intro s _
    by_cases hs : a s = 0 ∨ a s = n
    · exact Submodule.smul_mem _ _ (hbasis_mem s hs)
    · have ha0 : a s ≠ 0 := fun h => hs (Or.inl h)
      have han : a s ≠ n := fun h => hs (Or.inr h)
      have halt : a s < n := lt_of_le_of_ne (ha_le s) han
      have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
      have hdiff : (n : ℂ) - (a s : ℂ) ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast han.symm)
      have hscalar : (4 : ℂ) * (a s : ℂ) * ((n : ℂ) - (a s : ℂ)) * (d : ℂ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast ha0))
          hdiff) hd0
      have hy0 : derivationKernelOperator A k y = 0 := LinearMap.mem_ker.mp hy
      have hcoord := congrArg (fun z => B.repr z s) hy0
      rw [show y = ∑ t, B.repr y t • B t by
        symm
        simpa [B] using B.sum_repr y] at hcoord
      simp only [map_sum, map_smul] at hcoord
      have hdiag (t : Set.powersetCard (Fin (n + n)) n) :
          derivationKernelOperator A k (B t) =
            ((4 : ℂ) * (a t : ℂ) * ((n : ℂ) - (a t : ℂ)) * (d : ℂ)) • B t := by
        simpa [B, n, a] using
          A.derivationKernelOperator_adapted_exterior_basis hd k b hb t
      simp_rw [hdiag] at hcoord
      simp only [smul_smul, map_smul, map_zero] at hcoord
      have hcoeff : B.repr y s *
          ((4 : ℂ) * (a s : ℂ) * ((n : ℂ) - (a s : ℂ)) * (d : ℂ)) = 0 := by
        simpa only [B, Finsupp.finsetSum_apply, Finsupp.smul_apply,
          Module.Basis.repr_self, Finsupp.single_apply, Pi.zero_apply, smul_eq_mul,
          Finsupp.zero_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_eq_left] using hcoord
      have : B.repr y s = 0 := (mul_eq_zero.mp hcoeff).resolve_right hscalar
      simp [this]
  · simpa [k] using A.eigenspace_sup_le_ker_middle hd

/-- Degree-zero sanity check for the kernel identity statement. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) (hd : 0 < d)
    (hk : Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) = 0) :
    LinearMap.ker (derivationKernelOperator A 0) =
      LinearMap.range (exteriorPower.map (0 + 0) A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map (0 + 0) A.Vsbar.subtype) := by
  have h := A.ker_derivationKernelOperator_eq_sup hH hWeil hd
  rw [hk] at h
  simpa using h

end WeilAction

#print axioms WeilAction.finrank_Vs_eq_twice_inf_H10
#print axioms WeilAction.finrank_Vsbar_eq_Vs
#print axioms WeilAction.eigenspace_sup_le_ker_middle
#print axioms WeilAction.exists_adapted_Jc_basis
#print axioms WeilAction.sum_ite_eq_card_filter_sub
#print axioms WeilAction.derivationExt_adapted_exterior_basis
#print axioms WeilAction.derivationKernelOperator_adapted_exterior_basis
#print axioms WeilAction.ker_derivationKernelOperator_eq_sup

end HodgeBlocks

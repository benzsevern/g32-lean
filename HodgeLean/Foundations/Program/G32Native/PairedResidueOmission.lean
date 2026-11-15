import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Field

/-! # The linear residue calculation for a pencil with one omitted pair -/

noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

variable {K : Type*} [Field K] {r : ℕ}

/-- Total residue, with the two entries of each marked pair retained. -/
def pencilTotalResidue : (Fin r → K × K) →ₗ[K] K where
  toFun v := ∑ i, ((v i).1 + (v i).2)
  map_add' v w := by
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
    simp only [add_add_add_comm, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_add,
      Finset.smul_sum, RingHom.id_apply]

/-- The residue space of differentials supported on the marked pairs. -/
def pencilResidueSpace (K : Type*) [Field K] (r : ℕ) :
    Submodule K (Fin r → K × K) := LinearMap.ker pencilTotalResidue

/-- Pair sums at every index except the specified distinguished pair. -/
def pencilRetainedPairSums (j : Fin r) :
    pencilResidueSpace K r →ₗ[K] ({i : Fin r // i ≠ j} → K) where
  toFun v i := (v.val i).1 + (v.val i).2
  map_add' v w := by
    funext i
    exact add_add_add_comm _ _ _ _
  map_smul' c v := by
    funext i
    change c • (v.val i).1 + c • (v.val i).2 = c • ((v.val i).1 + (v.val i).2)
    exact (smul_add c (v.val i).1 (v.val i).2).symm

/-- The residue theorem forces the omitted relation from all the retained ones.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(i), pp. 13–14. -/
theorem pencil_omitted_pair_sum (j : Fin r) (v : pencilResidueSpace K r)
    (hv : pencilRetainedPairSums j v = 0) :
    (v.val j).1 + (v.val j).2 = 0 := by
  have ht : ∑ i, ((v.val i).1 + (v.val i).2) = 0 := v.property
  have hs : ∑ i, ((v.val i).1 + (v.val i).2) =
      (v.val j).1 + (v.val j).2 := by
    apply Finset.sum_eq_single j
    · intro i _ hij
      exact congrFun hv ⟨i, hij⟩
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  exact hs.symm.trans ht

/-- Every retained pair sum can be specified independently: the distinguished
pair absorbs the total residue. The sign in that correction is retained. -/
theorem pencil_retained_pair_sums_surjective (j : Fin r) :
    Function.Surjective (pencilRetainedPairSums (K := K) j) := by
  classical
  intro a
  let t : Fin r → K := fun i => if h : i = j then 0 else a ⟨i, h⟩
  let v : Fin r → K × K := fun i =>
    (t i - if i = j then ∑ q, t q else 0, 0)
  have hv : v ∈ pencilResidueSpace K r := by
    change (∑ i, ((v i).1 + (v i).2)) = 0
    simp only [v, add_zero, Finset.sum_sub_distrib]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, sub_self]
  refine ⟨⟨v, hv⟩, ?_⟩
  funext i
  change t i.val - (if i.val = j then ∑ q, t q else 0) + 0 = a i
  simp only [i.property, ite_false, sub_zero, add_zero, t, dite_eq_right i.property]

/-- Paired opposite residues give a linear parametrization of the fibre of
all retained pair sums over zero, with the positive residues as coordinates. -/
def pencilPairedResidueEquiv (j : Fin r) :
    (Fin r → K) ≃ₗ[K] LinearMap.ker (pencilRetainedPairSums (K := K) j) where
  toFun a := ⟨⟨fun i => (-a i, a i), by
    change (∑ i, (-a i + a i)) = 0
    simp only [neg_add_cancel, Finset.sum_const_zero]⟩, by
      ext i
      exact neg_add_cancel _⟩
  invFun v i := (v.val.val i).2
  left_inv a := rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply Prod.ext
    · have hi : (v.val.val i).1 + (v.val.val i).2 = 0 := by
        by_cases hij : i = j
        · subst i
          exact pencil_omitted_pair_sum j v.val v.property
        · exact congrFun v.property ⟨i, hij⟩
      exact (eq_neg_of_add_eq_zero_left hi).symm
    · rfl
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact Prod.ext (neg_add _ _) rfl
  map_smul' c a := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact Prod.ext (smul_neg c (a i)).symm rfl

/-- The zero fibre has one independent coefficient for each marked pair. -/
theorem pencil_retained_pair_sums_kernel_finrank (j : Fin r) :
    Module.finrank K (LinearMap.ker (pencilRetainedPairSums (K := K) j)) = r := by
  rw [← (pencilPairedResidueEquiv (K := K) j).finrank_eq]
  exact Module.finrank_fin_fun K

end HodgeLean.Foundations.Program.G32Native

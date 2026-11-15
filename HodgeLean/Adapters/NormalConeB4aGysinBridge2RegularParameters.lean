import HodgeLean.Foundations.DivisorClassHodgeRegular
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Reformulated bridge of A3-B4a: regular systems of parameters

In a regular local ring of dimension `n`, a list of `n` elements generating the maximal ideal is a
weakly regular sequence. Source: Matsumura, *Commutative Ring Theory*, Theorem 14.3 and
Theorem 17.4. -/

noncomputable section
namespace HodgeLean.Adapters
open IsLocalRing RingTheory.Sequence HodgeLean.Foundations Pointwise

universe u

/-- A list of `dim R` generators of the maximal ideal of a regular local ring `R` is weakly
regular. Source: Matsumura, *Commutative Ring Theory*, Theorem 14.3 and Theorem 17.4. -/
theorem a3b4g_isWeaklyRegular_of_ofList_eq_maximalIdeal : ∀ (n : ℕ) (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (xs : List R), ringKrullDim R = n → xs.length = n →
      Ideal.ofList xs = maximalIdeal R → IsWeaklyRegular R xs := by
  classical
  intro n
  induction n with
  | zero =>
    intro R _ _ xs _ hlen _
    rw [List.length_eq_zero_iff.mp hlen]
    exact IsWeaklyRegular.nil R R
  | succ m ih =>
    intro R _ _ xs hdim hlen hgen
    obtain ⟨x, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    have hys : ys.length = m := by simpa using hlen
    have hx : x ∈ maximalIdeal R := hgen ▸ Ideal.subset_span List.mem_cons_self
    have hfg : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
    have hx2 : x ∉ maximalIdeal R ^ 2 := by
      intro hx2
      have h1 : Ideal.span {x} ≤ maximalIdeal R • maximalIdeal R := by
        rw [Ideal.span_le, Set.singleton_subset_iff, smul_eq_mul, ← pow_two]
        exact hx2
      have hle : maximalIdeal R ≤ Ideal.ofList ys ⊔ maximalIdeal R • maximalIdeal R := by
        calc maximalIdeal R = Ideal.ofList (x :: ys) := hgen.symm
          _ = Ideal.span {x} ⊔ Ideal.ofList ys := Ideal.ofList_cons x ys
          _ ≤ _ := sup_le (h1.trans le_sup_right) le_sup_left
      have hjac : maximalIdeal R ≤ Ideal.jacobson ⊥ :=
        (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
      have hm : maximalIdeal R = Ideal.ofList ys := by
        refine le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hle) ?_
        rw [← hgen, Ideal.ofList_cons x ys]
        exact le_sup_right
      have hrank := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
      have hspan : (maximalIdeal R).spanFinrank ≤ m := by
        rw [hm]
        refine (Submodule.spanFinrank_span_le_ncard_of_finite (List.finite_toSet ys)).trans ?_
        rw [← hys]
        have : {r | r ∈ ys} = (ys.toFinset : Set R) := by ext; simp
        rw [this, Set.ncard_coe_finset]
        exact List.toFinset_card_le ys
      rw [hdim] at hrank
      have : (maximalIdeal R).spanFinrank = m + 1 := by exact_mod_cast hrank
      omega
    have hdom : IsDomain R := dcl_isDomain_of_ringKrullDim_eq (m + 1) R hdim
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx2 (Submodule.zero_mem _)
    have hmin : ∀ p ∈ minimalPrimes R, x ∉ p := by
      intro p hp hxp
      rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hp
      subst hp
      exact hx0 hxp
    letI := dcl_quotient_isLocalRing hx
    letI : IsRegularLocalRing (R ⧸ Ideal.span {x}) := dcl_quotient_isRegularLocalRing hx hx2 hmin
    have hdim' : ringKrullDim (R ⧸ Ideal.span {x}) = m := by
      have h := dcl_ringKrullDim_quotient_succ hx hmin
      obtain ⟨e, he⟩ := dcl_exists_ringKrullDim_eq_natCast (R ⧸ Ideal.span {x})
      rw [he, hdim] at h
      have : e + 1 = m + 1 := by exact_mod_cast h
      rw [he]
      exact_mod_cast (by omega : e = m)
    have hgen' : Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span {x}))) =
        maximalIdeal (R ⧸ Ideal.span {x}) := by
      rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← hgen,
        Ideal.map_ofList, List.map_cons, Ideal.ofList_cons,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x),
        Ideal.span_singleton_zero, bot_sup_eq]
    have hreg' := ih (R ⧸ Ideal.span {x}) (ys.map (Ideal.Quotient.mk (Ideal.span {x}))) hdim'
      (by rw [List.length_map, hys]) hgen'
    have hreg'' : IsWeaklyRegular (R ⧸ Ideal.span {x}) ys :=
      (isWeaklyRegular_map_algebraMap_iff (R := R) (S := R ⧸ Ideal.span {x})
        (M := R ⧸ Ideal.span {x}) ys).mp hreg'
    have hq : (Ideal.span {x} : Submodule R R) = x • (⊤ : Submodule R R) := by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
    rw [isWeaklyRegular_cons_iff]
    refine ⟨fun a b hab => mul_left_cancel₀ hx0 hab, ?_⟩
    exact ((Submodule.quotEquivOfEq _ _ hq).isWeaklyRegular_congr ys).mp hreg''

end HodgeLean.Adapters

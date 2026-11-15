import HodgeLean.Foundations.Curves.AbelTheorem.SymplecticIntegral

noncomputable section
open Module Set
open scoped BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000

variable {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M]

theorem integral_symplectic_families (Q : LinearMap.BilinForm ℤ M)
    (hQ : ∀ x, Q x x = 0) (hS : Function.Surjective Q) :
    ∃ (m : ℕ) (e f : Fin m → M),
      (∀ i j, Q (e i) (f j) = if i = j then 1 else 0) ∧
      (∀ i j, Q (e i) (e j) = 0) ∧
      (∀ i j, Q (f i) (f j) = 0) ∧
      ⊤ ≤ Submodule.span ℤ (range e ∪ range f) := by
  classical
  generalize hn : finrank ℤ M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hn0 : n = 0
    · haveI : Subsingleton M := (Module.finrank_eq_zero_iff_of_free ℤ M).mp (hn.trans hn0)
      refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0,
        fun i => i.elim0, fun i => i.elim0, ?_⟩
      intro z hz
      rw [show z = 0 from Subsingleton.elim _ _]
      exact Submodule.zero_mem _
    have hp : 0 < finrank ℤ M := by omega
    let b := Module.finBasis ℤ M
    let j : Fin (finrank ℤ M) := ⟨0, hp⟩
    obtain ⟨x, hxy⟩ := integral_pair_of_basis_coordinate b j Q hS
    let y := b j
    have hyx : Q y x = -1 := by rw [integral_alternating_skew Q hQ, hxy]
    let K : Submodule ℤ M := LinearMap.ker (Q x) ⊓ LinearMap.ker (Q y)
    have hlt : finrank ℤ K < n := by
      rw [← hn]
      exact integral_pair_complement_rank_lt Q hQ x y hxy
    have hKS : Function.Surjective (Q.restrict K) :=
      integral_pair_complement_surjective Q hQ hS x y hxy
    obtain ⟨m, e', f', hef', hee', hff', hspan⟩ :=
      ih (finrank ℤ K) hlt (M := K) (Q.restrict K) (fun z => hQ z.val) hKS rfl
    let e : Fin m → M := fun i => (e' i).val
    let f : Fin m → M := fun i => (f' i).val
    have hef : ∀ i j, Q (e i) (f j) = if i = j then 1 else 0 := hef'
    have hee : ∀ i j, Q (e i) (e j) = 0 := hee'
    have hff : ∀ i j, Q (f i) (f j) = 0 := hff'
    have hxe : ∀ i, Q x (e i) = 0 := fun i => (e' i).property.1
    have hxf : ∀ i, Q x (f i) = 0 := fun i => (f' i).property.1
    have hye : ∀ i, Q y (e i) = 0 := fun i => (e' i).property.2
    have hyf : ∀ i, Q y (f i) = 0 := fun i => (f' i).property.2
    have hanti := integral_alternating_skew Q hQ
    refine ⟨m + 1, Fin.cons x e, Fin.cons y f, ?_, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.cases (Fin.cases ?_ (fun j => ?_) j)
        (fun i => Fin.cases ?_ (fun j => ?_) j) i
      · simpa only [Fin.cons_zero, ite_true] using hxy
      · simp [hxf, (Fin.succ_ne_zero j).symm]
      · simp [hanti (e i), hye, Fin.succ_ne_zero i]
      · simp [hef]
    · intro i j
      refine Fin.cases (Fin.cases ?_ (fun j => ?_) j)
        (fun i => Fin.cases ?_ (fun j => ?_) j) i
      · simp [hQ]
      · simp [hxe]
      · simp [hanti (e i), hxe]
      · simp [hee]
    · intro i j
      refine Fin.cases (Fin.cases ?_ (fun j => ?_) j)
        (fun i => Fin.cases ?_ (fun j => ?_) j) i
      · simp [hQ]
      · simp [hyf]
      · simp [hanti (f i), hyf]
      · simp [hff]
    · let S := Submodule.span ℤ
        (range (Fin.cons x e : Fin (m + 1) → M) ∪ range (Fin.cons y f))
      have hKm (z : K) : z.val ∈ S := by
        have hz := hspan (show z ∈ (⊤ : Submodule ℤ K) from trivial)
        induction hz using Submodule.span_induction with
        | mem u hu =>
          rcases hu with ⟨i, rfl⟩ | ⟨i, rfl⟩
          · exact Submodule.subset_span (Or.inl ⟨i.succ, by simp [e]⟩)
          · exact Submodule.subset_span (Or.inr ⟨i.succ, by simp [f]⟩)
        | zero => exact S.zero_mem
        | add u v hu hv ihu ihv => exact S.add_mem ihu ihv
        | smul r u hu ihu => exact S.smul_mem r ihu
      have hx : x ∈ S := Submodule.subset_span (Or.inl ⟨0, by simp⟩)
      have hy : y ∈ S := Submodule.subset_span (Or.inr ⟨0, by simp⟩)
      intro u hu
      have hr := hKm (integralPairProjection Q hQ x y hxy u)
      change u + Q y u • x - Q x u • y ∈ S at hr
      have heq : u = (u + Q y u • x - Q x u • y) - Q y u • x + Q x u • y := by abel
      rw [heq]
      exact S.add_mem (S.sub_mem hr (S.smul_mem _ hx)) (S.smul_mem _ hy)

theorem integral_symplectic_basis (Q : LinearMap.BilinForm ℤ M)
    (hQ : ∀ x, Q x x = 0) (hS : Function.Surjective Q) :
    ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) ℤ M),
      (∀ i j, Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0) ∧
      (∀ i j, Q (b (.inl i)) (b (.inl j)) = 0) ∧
      (∀ i j, Q (b (.inr i)) (b (.inr j)) = 0) := by
  classical
  obtain ⟨m, e, f, hef, hee, hff, hspan⟩ := integral_symplectic_families Q hQ hS
  have hfe : ∀ i j, Q (f i) (e j) = -(if j = i then 1 else 0) := by
    intro i j
    rw [integral_alternating_skew Q hQ, hef]
  have hli : LinearIndependent ℤ (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rintro (i | i)
    · have he := congrArg (fun z => Q z (f i)) hg
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_add, map_sum,
        map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, hef, hff, mul_zero, Finset.sum_const_zero, add_zero,
        map_zero, LinearMap.zero_apply] at he
      simpa [mul_ite] using he
    · have he := congrArg (fun z => Q (e i) z) hg
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_add, map_sum,
        map_smul, smul_eq_mul, hef, hee, mul_zero, Finset.sum_const_zero,
        zero_add, map_zero] at he
      simpa [mul_ite, eq_comm] using he
  have hsp : ⊤ ≤ Submodule.span ℤ (range (Sum.elim e f)) := by
    rw [Set.Sum.elim_range]
    exact hspan
  let b := Basis.mk hli hsp
  refine ⟨m, b, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩ <;>
    simp [b, hef, hee, hff]

end HodgeLean.Foundations.Curves.AbelTheorem

import HodgeLean.Foundations.Program.SchoenCycleDivisorSymmetric
import HodgeLean.Foundations.Program.SchoenCycleTupleMultiplicity

/-! # Integer divisors of finite tuples
Enumerations retain the actual integer multiplicities used in the canonical-system clause.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Integer multiplicities of a tuple equal the sum of its point divisors. -/
theorem s2e_tuple_integer_divisor {C : Type*} [DecidableEq C] {n : ℕ}
    (f : Fin n → C) :
    (List.ofFn f : Multiset C).toFinsupp.mapRange (fun m : ℕ => (m : ℤ)) rfl =
      ∑ i, Finsupp.single (f i) (1 : ℤ) := by
  ext p
  simp only [Finsupp.mapRange_apply, Multiset.toFinsupp_apply, Multiset.coe_count,
    s2e_tuple_count_eq_fiber_card, Fintype.card_subtype, Finsupp.finset_sum_apply,
    Finsupp.single_apply]
  simp

/-- Every effective divisor of degree n is the integer sum of an actual n-tuple of points. -/
theorem s2e_effectiveDivisor_exists_tuple {C : Type} {n : ℕ}
    (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (hd : b4c_deg D = (n : ℤ)) :
    ∃ f : Fin n → C, D = ∑ i, Finsupp.single (f i) (1 : ℤ) := by
  classical
  obtain ⟨f, hf⟩ := s2e_sym_exists_enumeration (s2e_divisorSym D hD hd)
  have hr := s2e_divisorSym_recover D hD hd
  rw [← hf, s2e_tuple_integer_divisor] at hr
  exact ⟨f, hr.symm⟩

/-- An exact integer point sum is an enumeration of the effective divisor's unordered tuple. -/
theorem s2e_divisor_tuple_enumeration {C : Type} {n : ℕ}
    (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (hd : b4c_deg D = (n : ℤ))
    (f : Fin n → C) (hf : D = ∑ i, Finsupp.single (f i) (1 : ℤ)) :
    (List.ofFn f : Multiset C) = s2e_divisorSym D hD hd := by
  classical
  apply Multiset.toFinsupp.injective
  apply Finsupp.mapRange_injective (fun m : ℕ => (m : ℤ)) rfl (by intro a b h; change (a : ℤ) = (b : ℤ) at h; omega)
  rw [s2e_tuple_integer_divisor, ← hf, s2e_divisorSym_recover]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Distinct positive coefficients exhaust an effective divisor of the same degree. -/
theorem s2e_effectiveDivisor_eq_distinct_tuple {C : Type} {n : ℕ}
    (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (hd : b4c_deg D = (n : ℤ))
    (f : Fin n → C) (hf : Function.Injective f) (hpos : ∀ i, 0 < D (f i)) :
    D = ∑ i, Finsupp.single (f i) (1 : ℤ) := by
  classical
  let s := s2e_divisorSym D hD hd
  have hn : (List.ofFn f : Multiset C).Nodup := by
    simpa using List.nodup_ofFn_ofInjective hf
  have hl : (List.ofFn f : Multiset C) ≤ (s : Multiset C) := by
    apply (Multiset.le_iff_subset hn).mpr
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact (s2e_divisorSym_mem_iff D hD hd (f i)).mpr (hpos i)
  have he : (List.ofFn f : Multiset C) = (s : Multiset C) :=
    Multiset.eq_of_le_of_card_le hl (by
      have hs : (s : Multiset C).card = n := s.property
      have hfcard : (List.ofFn f : Multiset C).card = n := by simp
      omega)
  have hr := s2e_divisorSym_recover D hD hd
  rw [← he, s2e_tuple_integer_divisor] at hr
  exact hr.symm

/-- A tuple with bounded multiplicities exhausts an effective divisor of the same degree. -/
theorem s2e_effectiveDivisor_eq_tuple_of_le {C : Type} {n : ℕ}
    (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (hd : b4c_deg D = (n : ℤ))
    (f : Fin n → C) (hle : (∑ i, Finsupp.single (f i) (1 : ℤ)) ≤ D) :
    D = ∑ i, Finsupp.single (f i) (1 : ℤ) := by
  classical
  obtain ⟨g, hg⟩ := s2e_effectiveDivisor_exists_tuple D hD hd
  have hl : (List.ofFn f : Multiset C) ≤ (List.ofFn g : Multiset C) := by
    apply Multiset.le_iff_count.mpr
    intro p
    have hp := hle p
    rw [hg, ← s2e_tuple_integer_divisor, ← s2e_tuple_integer_divisor] at hp
    simp only [Finsupp.mapRange_apply, Multiset.toFinsupp_apply] at hp
    exact_mod_cast hp
  have he : (List.ofFn f : Multiset C) = List.ofFn g :=
    Multiset.eq_of_le_of_card_le hl (by simp)
  rw [hg, ← s2e_tuple_integer_divisor, ← s2e_tuple_integer_divisor, he]

/-- Injective local coordinates transport root-count bounds to an effective divisor bound. -/
theorem s2e_tuple_divisor_le_of_injective_coordinates {A C : Type} [DecidableEq A] {n : ℕ}
    (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (U : Set A) (g : A → C)
    (hg : Set.InjOn g U) (z : Fin n → A) (hz : ∀ i, z i ∈ U)
    (hm : ∀ w ∈ U, (Fintype.card {i : Fin n // z i = w} : ℤ) ≤ D (g w)) :
    (∑ i, Finsupp.single (g (z i)) (1 : ℤ)) ≤ D := by
  classical
  intro p
  by_cases hp : ∃ i, g (z i) = p
  · obtain ⟨i, rfl⟩ := hp
    have he : Fintype.card {j : Fin n // g (z j) = g (z i)} =
        Fintype.card {j : Fin n // z j = z i} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun j => ⟨fun h => hg (hz j) (hz i) h,
        fun h => congrArg g h⟩)
    rw [← s2e_tuple_integer_divisor]
    simp only [Finsupp.mapRange_apply, Multiset.toFinsupp_apply, Multiset.coe_count]
    rw [s2e_tuple_count_eq_fiber_card, he]
    exact hm (z i) (hz i)
  · have hzero : (∑ i, Finsupp.single (g (z i)) (1 : ℤ)) p = 0 := by
      simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun h => hp ⟨i, h⟩)
    rw [hzero]
    exact hD p

/-- Divisors in disjoint clusters stay bounded when their local bounds are assembled. -/
theorem s2e_disjoint_divisor_sum_le {ι C : Type} [Fintype ι]
    (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (A : ι → C →₀ ℤ)
    (hA : ∀ i, A i ≤ D)
    (hdis : Pairwise (fun i j => Disjoint (A i).support (A j).support)) :
    (∑ i, A i) ≤ D := by
  classical
  intro p
  simp only [Finsupp.finsetSum_apply]
  by_cases hp : ∃ i, A i p ≠ 0
  · obtain ⟨i, hi⟩ := hp
    rw [Finset.sum_eq_single i]
    · exact hA i p
    · intro j _ hji
      by_contra hj
      exact (Finset.disjoint_left.mp (hdis hji))
        (Finsupp.mem_support_iff.mpr hj) (Finsupp.mem_support_iff.mpr hi)
    · simp
  · have hz : ∀ i, A i p = 0 := by simpa only [not_exists, not_not] using hp
    simp only [hz, Finset.sum_const_zero]
    exact hD p

/-- Multiplicity exhaustion works for any finite indexing type. -/
theorem s2e_effectiveDivisor_eq_finite_tuple_of_le {ι C : Type} [Fintype ι]
    (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (hd : b4c_deg D = (Fintype.card ι : ℤ))
    (f : ι → C) (hle : (∑ i, Finsupp.single (f i) (1 : ℤ)) ≤ D) :
    D = ∑ i, Finsupp.single (f i) (1 : ℤ) := by
  classical
  let e := Fintype.equivFin ι
  have he : (∑ i, Finsupp.single (f (e.symm i)) (1 : ℤ)) =
      ∑ i, Finsupp.single (f i) (1 : ℤ) := e.symm.sum_comp (fun i => Finsupp.single (f i) (1 : ℤ))
  have hh := s2e_effectiveDivisor_eq_tuple_of_le D hD hd (fun i => f (e.symm i))
    (by rw [he]; exact hle)
  exact hh.trans he

/-- Disjoint local tuples with full total degree exhaust an effective divisor. -/
theorem s2e_effectiveDivisor_eq_cluster_sum {ι C : Type} [Fintype ι]
    (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (d : ι → ℕ)
    (hd : b4c_deg D = ((∑ i, d i : ℕ) : ℤ)) (f : (i : ι) → Fin (d i) → C)
    (hlocal : ∀ i, (∑ j, Finsupp.single (f i j) (1 : ℤ)) ≤ D)
    (hdis : Pairwise (fun i k => Disjoint
      (∑ j, Finsupp.single (f i j) (1 : ℤ)).support
      (∑ j, Finsupp.single (f k j) (1 : ℤ)).support)) :
    D = ∑ i, ∑ j, Finsupp.single (f i j) (1 : ℤ) := by
  classical
  have hsum := s2e_disjoint_divisor_sum_le D hD
    (fun i => ∑ j, Finsupp.single (f i j) (1 : ℤ)) hlocal hdis
  have hd' : b4c_deg D = (Fintype.card (Σ i, Fin (d i)) : ℤ) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hd
  have he := s2e_effectiveDivisor_eq_finite_tuple_of_le D hD hd'
    (fun ij : Σ i, Fin (d i) => f ij.1 ij.2)
    (by simpa only [Fintype.sum_sigma] using hsum)
  simpa only [Fintype.sum_sigma] using he

end HodgeLean.Foundations.Program

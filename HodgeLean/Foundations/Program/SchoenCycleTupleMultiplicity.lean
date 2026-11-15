import Mathlib.Data.Sym.Basic
import Mathlib.Data.Fintype.EquivFin

/-! # Reordering tuples with repeated entries
Equal multiplicities supply a permutation of the coordinate indices.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The multiplicity of a point in a tuple is the cardinality of its index fiber. -/
theorem s2e_tuple_count_eq_fiber_card {A : Type*} [DecidableEq A]
    {n : ℕ} (f : Fin n → A) (a : A) :
    (List.ofFn f).count a = Fintype.card {i // f i = a} := by
  rw [Fintype.card_subtype, List.ofFn_eq_map, List.count, List.countP_map]
  have h := (List.nodup_finRange n).card_eq_countP (P := fun i => f i = a)
  simpa only [List.toFinset_finRange, Function.comp_def, Bool.beq_eq_decide_eq] using h.symm

/-- Tuples representing the same multiset differ by an index permutation,
including when some entries repeat. -/
theorem s2e_tuple_permutation_of_multiset_eq {A : Type*} {n : ℕ}
    (f g : Fin n → A) (h : (List.ofFn f : Multiset A) = List.ofFn g) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, g (σ i) = f i := by
  classical
  have hc (a : A) : Fintype.card {i // f i = a} = Fintype.card {i // g i = a} := by
    rw [← s2e_tuple_count_eq_fiber_card f a, ← s2e_tuple_count_eq_fiber_card g a]
    simpa only [Multiset.coe_count] using congrArg (Multiset.count a) h
  let e (a : A) : {i // f i = a} ≃ {i // g i = a} := Fintype.equivOfCardEq (hc a)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

/-- Every unordered n-tuple has an enumeration by Fin n. -/
theorem s2e_sym_exists_enumeration {A : Type*} {n : ℕ} (s : Sym A n) :
    ∃ f : Fin n → A, (List.ofFn f : Multiset A) = s := by
  obtain ⟨l, hl⟩ := Quotient.exists_rep (s : Multiset A)
  change (l : Multiset A) = (s : Multiset A) at hl
  have hn : l.length = n := (congrArg Multiset.card hl).trans s.property
  subst n
  exact ⟨l.get, by simpa only [List.ofFn_get] using hl⟩

/-- Choose an ordering of an actual unordered tuple, retaining repetitions.
Source: Mathlib `Sym`, the multiset model of finite symmetric powers. -/
def s2e_symEnumeration {A : Type*} {n : ℕ} (s : Sym A n) : Fin n → A :=
  (s2e_sym_exists_enumeration s).choose

example {A : Type*} {n : ℕ} (s : Sym A n) :
    (List.ofFn (s2e_symEnumeration s) : Multiset A) = s :=
  (s2e_sym_exists_enumeration s).choose_spec

/-- Mapping an enumeration gives an enumeration of the mapped unordered tuple. -/
theorem s2e_sym_map_enumeration {A B : Type*} {n : ℕ}
    (s : Sym A n) (f : Fin n → A) (hf : (List.ofFn f : Multiset A) = s)
    (g : A → B) :
    (List.ofFn (fun i => g (f i)) : Multiset B) = s.map g := by
  change (List.ofFn (g ∘ f) : Multiset B) = s.map g
  rw [← List.map_ofFn, ← Multiset.map_coe, hf, Sym.coe_map]

end HodgeLean.Foundations.Program

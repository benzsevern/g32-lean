import HodgeLean.Foundations.Program.RigidStartingSystemDefs
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem b65r_telescoping {A : Type*} [Ring A] (xs : List A) :
    ∑ k ∈ Finset.range xs.length,
      (xs.take k).prod * (xs.getD k 1 - 1) = xs.prod - 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.length_cons, Finset.sum_range_succ', List.take_succ_cons,
        List.prod_cons, List.getD_cons_succ, List.take_zero, List.prod_nil,
        List.getD_cons_zero, one_mul]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ih]
      noncomm_ring

def b65r_prefix {A : Type*} [Monoid A] {r : ℕ} (F : Fin r → A) (k : ℕ) : A :=
  ((List.ofFn F).take k).prod

theorem b65r_prefix_succ {A : Type*} [Monoid A] {r : ℕ}
    (F : Fin r → A) (i : Fin r) :
    b65r_prefix F (i.val+1) = b65r_prefix F i.val * F i := by
  unfold b65r_prefix
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using i.isLt),
    List.prod_append, List.prod_singleton, List.getElem_ofFn]

theorem b65r_prefix_sum {A : Type*} [Ring A] {r : ℕ} (F : Fin r → A) :
    ∑ i : Fin r, b65r_prefix F i.val * (F i-1) = (List.ofFn F).prod-1 := by
  have ht := b65r_telescoping (List.ofFn F)
  simp only [List.length_ofFn] at ht
  rw [← Fin.sum_univ_eq_sum_range] at ht
  simpa [b65r_prefix, List.getD_eq_getElem?_getD] using ht

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {r : ℕ}

def b65r_difference (F : Fin r → Module.End ℂ V) (i : Fin r) : Module.End ℂ V :=
  F i - LinearMap.id

abbrev b65r_localSpace (F : Fin r → Module.End ℂ V) :=
  ∀ i : Fin r, LinearMap.range (b65r_difference F i)

def b65r_coboundary (F : Fin r → Module.End ℂ V) : V →ₗ[ℂ] b65r_localSpace F :=
  LinearMap.pi (fun i ↦ (b65r_difference F i).rangeRestrict)

def b65r_sumMap (F : Fin r → Module.End ℂ V) : b65r_localSpace F →ₗ[ℂ] V :=
  ∑ i : Fin r, (b65r_prefix F i.val).comp
    ((LinearMap.range (b65r_difference F i)).subtype.comp (LinearMap.proj i))

theorem b65r_sumMap_coboundary (F : Fin r → Module.End ℂ V)
    (hp : (List.ofFn F).prod = 1) :
    (b65r_sumMap F).comp (b65r_coboundary F) = 0 := by
  ext v
  have he := congrArg (fun L : Module.End ℂ V ↦ L v) (b65r_prefix_sum F)
  rw [hp, sub_self] at he
  change (∑ i : Fin r, (b65r_prefix F i.val).comp
    ((LinearMap.range (b65r_difference F i)).subtype.comp (LinearMap.proj i)))
      (b65r_coboundary F v) = 0
  rw [LinearMap.sum_apply]
  change ∑ i : Fin r, b65r_prefix F i.val ((F i - 1) v) = 0
  simpa only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.zero_apply] using he

theorem b65r_sumMap_single (F : Fin r → Module.End ℂ V) (i : Fin r)
    (x : LinearMap.range (b65r_difference F i)) :
    b65r_sumMap F (Pi.single i x) = b65r_prefix F i.val x.val := by
  classical
  simp only [b65r_sumMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
    rfl
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    simp
  · simp

theorem b65r_coboundary_injective (F : Fin r → Module.End ℂ V)
    (hfix : ∀ v : V, (∀ i, F i v = v) → v = 0) :
    Function.Injective (b65r_coboundary F) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply hfix v
  intro i
  have he := congrArg (fun x : b65r_localSpace F ↦ (x i).val) hv
  change F i v - v = 0 at he
  exact sub_eq_zero.mp he

theorem b65r_sumMap_dual_fixed (F : Fin r → Module.End ℂ V)
    (f : Module.Dual ℂ V) (hf : f.comp (b65r_sumMap F) = 0) :
    ∀ i, f.comp (F i) = f := by
  classical
  have hterm (i : Fin r) (v : V) :
      f (b65r_prefix F i.val ((F i-1) v)) = 0 := by
    have he := congrArg (fun L : b65r_localSpace F →ₗ[ℂ] ℂ ↦
      L (Pi.single i ((b65r_difference F i).rangeRestrict v))) hf
    simp only [LinearMap.comp_apply, b65r_sumMap_single, LinearMap.zero_apply] at he
    change f (b65r_prefix F i.val ((F i-1) v)) = 0 at he
    exact he
  have hprefix : ∀ k : ℕ, k ≤ r → ∀ v : V, f (b65r_prefix F k v) = f v := by
    intro k
    induction k with
    | zero => intro _ v; simp [b65r_prefix]
    | succ k ih =>
        intro hk v
        have hkr : k < r := Nat.lt_of_succ_le hk
        have he := hterm ⟨k,hkr⟩ v
        rw [ih (Nat.le_of_lt hkr)] at he
        change f (F ⟨k,hkr⟩ v-v) = 0 at he
        rw [map_sub] at he
        rw [b65r_prefix_succ F ⟨k,hkr⟩]
        change f (b65r_prefix F k (F ⟨k,hkr⟩ v)) = f v
        rw [ih (Nat.le_of_lt hkr)]
        exact sub_eq_zero.mp he
  intro i
  ext v
  have he := hterm i v
  rw [hprefix i.val (Nat.le_of_lt i.isLt)] at he
  change f (F i v-v) = 0 at he
  rw [map_sub] at he
  exact sub_eq_zero.mp he

theorem b65r_sumMap_surjective (F : Fin r → Module.End ℂ V)
    (hdual : ∀ f : Module.Dual ℂ V, (∀ i, f.comp (F i) = f) → f = 0) :
    Function.Surjective (b65r_sumMap F) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  apply hdual f
  exact b65r_sumMap_dual_fixed F f hf

theorem b65r_scott_bound [FiniteDimensional ℂ V]
    (F : Fin r → Module.End ℂ V) (hp : (List.ofFn F).prod = 1)
    (hfix : ∀ v : V, (∀ i, F i v = v) → v = 0)
    (hdual : ∀ f : Module.Dual ℂ V, (∀ i, f.comp (F i) = f) → f = 0) :
    2*Module.finrank ℂ V ≤ ∑ i : Fin r,
      Module.finrank ℂ (LinearMap.range (b65r_difference F i)) := by
  have hz := b65r_sumMap_coboundary F hp
  let d : V →ₗ[ℂ] LinearMap.ker (b65r_sumMap F) :=
    LinearMap.codRestrict (LinearMap.ker (b65r_sumMap F)) (b65r_coboundary F)
      (fun v ↦ by
        change b65r_sumMap F (b65r_coboundary F v) = 0
        exact congrArg (fun L : V →ₗ[ℂ] V ↦ L v) hz)
  have hd : Function.Injective d := by
    intro v w h
    apply b65r_coboundary_injective F hfix
    exact congrArg Subtype.val h
  have hdim := LinearMap.finrank_le_finrank_of_injective hd
  have hrank := (b65r_sumMap F).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (b65r_sumMap_surjective F hdual), finrank_top] at hrank
  have hlocal : Module.finrank ℂ (b65r_localSpace F) =
      ∑ i : Fin r, Module.finrank ℂ (LinearMap.range (b65r_difference F i)) := by
    change Module.finrank ℂ (∀ i : Fin r, LinearMap.range (b65r_difference F i)) = _
    rw [Module.finrank_pi_fintype]
  rw [hlocal] at hrank
  omega

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupRegularSequence
import Mathlib.Data.List.OfFn

/-! # Relations between regular equations

This calculation retains every transverse equation. It works over a
commutative ring without a reducedness assumption on that ring.
-/

open scoped BigOperators
open RingTheory.Sequence
namespace HodgeLean.Foundations.Program.G32Native

/-- Every coefficient of a relation between a weakly regular sequence lies
in its generated ideal. This is the degree-one relation calculation used
when constructing the conormal frame.
Source: Hartshorne, Algebraic Geometry, II.8, regular immersions and their
conormal modules. -/
theorem paired_c3_regular_relation_coefficients
    {A : Type*} [CommRing A] {n : ℕ} (f c : Fin n → A)
    (hreg : IsWeaklyRegular A (List.ofFn f))
    (hzero : ∑ i, c i * f i = 0) :
    ∀ i, c i ∈ Ideal.span (Set.range f) := by
  classical
  induction n with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
    let g : Fin n → A := fun i => f i.castSucc
    let K : Ideal A := Ideal.span (Set.range g)
    have hlist : Ideal.ofList (List.ofFn g) = K := by
      apply congrArg Ideal.span
      ext x
      simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range]
    rw [List.ofFn_succ', List.concat_eq_append] at hreg
    obtain ⟨hg, ht⟩ := (isWeaklyRegular_append_iff A _ _).mp hreg
    have ht' : IsSMulRegular (A ⧸ (K • ⊤ : Submodule A A)) (f (Fin.last n)) := by
      change IsWeaklyRegular (A ⧸ (Ideal.ofList (List.ofFn g) • ⊤ : Submodule A A)) [f (Fin.last n)] at ht
      rw [hlist] at ht
      exact (isWeaklyRegular_singleton_iff _ _).mp ht
    have htop : (K • ⊤ : Submodule A A) = K := Ideal.mul_top K
    rw [htop] at ht'
    have hcK : c (Fin.last n) ∈ K := by
      apply mem_of_isSMulRegular_quotient_of_smul_mem ht'
      change f (Fin.last n) * c (Fin.last n) ∈ K
      have hsum : ∑ i : Fin n, c i.castSucc * f i.castSucc ∈ K :=
        K.sum_mem fun i _ => K.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩)
      rw [Fin.sum_univ_castSucc] at hzero
      have heq : f (Fin.last n) * c (Fin.last n) =
          -(∑ i : Fin n, c i.castSucc * f i.castSucc) := by
        rw [mul_comm]
        exact eq_neg_of_add_eq_zero_right hzero
      rw [heq]
      exact K.neg_mem hsum
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hcK
    have hz : ∑ i : Fin n, (c i.castSucc + b i * f (Fin.last n)) * g i = 0 := by
      simp only [add_mul, Finset.sum_add_distrib]
      have hb' : ∑ i, b i * f (Fin.last n) * g i =
          c (Fin.last n) * f (Fin.last n) := by
        simp_rw [mul_right_comm (b _) (f (Fin.last n))]
        rw [← Finset.sum_mul, hb]
      rw [hb']
      exact (Fin.sum_univ_castSucc (fun i => c i * f i)) ▸ hzero
    have hind := ih g (fun i => c i.castSucc + b i * f (Fin.last n)) hg hz
    have hK : K ≤ Ideal.span (Set.range f) := by
      apply Ideal.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.castSucc, rfl⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hK hcK
    · have hh := hK (hind j)
      have hl : b j * f (Fin.last n) ∈ Ideal.span (Set.range f) :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨Fin.last n, rfl⟩)
      simpa only [add_sub_cancel_right] using (Ideal.span (Set.range f)).sub_mem hh hl

#print axioms paired_c3_regular_relation_coefficients
end HodgeLean.Foundations.Program.G32Native

import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

noncomputable section
namespace HodgeLean.Foundations.Program
open HomogeneousLocalization

variable {A σ ι : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] [Fintype ι]
    {r : A} (hr : r ∈ G 1) (v : ι → A) (hv : ∀ i, v i ∈ G 1)

set_option backward.isDefEq.respectTransparency.types false in
theorem b54_away_monomial_eq_prod (e : ι → ℕ) (a : ℕ) (he : ∑ i, e i = a) :
    Away.mk G hr a (∏ i, v i ^ e i)
      (by convert SetLike.prod_pow_mem_graded G (fun _ ↦ (1 : ℕ)) v e
            (F := Finset.univ) (fun i _ ↦ hv i) using 1 <;> simp [he]) =
      ∏ i, (Away.mk G hr 1 (v i) (by simpa using hv i)) ^ e i := by
  classical
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, show (∏ i, (Away.mk G hr 1 (v i) (by simpa using hv i)) ^ e i).val =
      ∏ i, (Away.mk G hr 1 (v i) (by simpa using hv i)).val ^ e i by
    induction (Finset.univ : Finset ι) using Finset.induction with
    | empty => exact HomogeneousLocalization.val_one
    | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs, Finset.prod_insert hjs,
        HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, ih]]
  simp only [Away.val_mk]
  simp_rw [Localization.mk_pow]
  rw [Localization.mk_prod]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  simp [Finset.prod_pow_eq_pow_sum, he]

theorem b54_away_adjoin_ratios_eq_top
    (hgen : Algebra.adjoin (G 0) (Set.range v) = ⊤) :
    Algebra.adjoin (G 0)
      (Set.range (fun i ↦ Away.mk G hr 1 (v i) (by simpa using hv i))) = ⊤ := by
  classical
  rw [← top_le_iff, ← Away.adjoin_mk_prod_pow_eq_top hr ι v hgen
    (fun _ ↦ (1 : ℕ)) hv, Algebra.adjoin_le_iff]
  rintro x ⟨a, e, he, _, rfl⟩
  rw [b54_away_monomial_eq_prod G hr v hv e a (by simpa using he)]
  apply prod_mem
  intro i _
  apply pow_mem
  exact Algebra.subset_adjoin (Set.mem_range_self i)

theorem b54_away_surjective_of_ratios
    (hgen : Algebra.adjoin (G 0) (Set.range v) = ⊤)
    {D : Type*} [CommRing D] (f : D →+* Away G r)
    (hbase : ∀ c : G 0, algebraMap (G 0) (Away G r) c ∈ f.range)
    (hratios : ∀ i, Away.mk G hr 1 (v i) (by simpa using hv i) ∈ f.range) :
    Function.Surjective f := by
  intro x
  have hx : x ∈ Algebra.adjoin (G 0)
      (Set.range (fun i ↦ Away.mk G hr 1 (v i) (by simpa using hv i))) := by
    rw [b54_away_adjoin_ratios_eq_top G hr v hv hgen]
    trivial
  change x ∈ f.range
  induction hx using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hratios i
  | algebraMap c => exact hbase c
  | add x y _ _ hx hy => exact f.range.add_mem hx hy
  | mul x y _ _ hx hy => exact f.range.mul_mem hx hy

theorem b54_away_ringHom_ext
    (hgen : Algebra.adjoin (G 0) (Set.range v) = ⊤)
    {D : Type*} [CommRing D] (f g : Away G r →+* D)
    (hbase : ∀ c : G 0, f (algebraMap (G 0) (Away G r) c) =
      g (algebraMap (G 0) (Away G r) c))
    (hratios : ∀ i, f (Away.mk G hr 1 (v i) (by simpa using hv i)) =
      g (Away.mk G hr 1 (v i) (by simpa using hv i))) : f = g := by
  ext x
  have hx : x ∈ Algebra.adjoin (G 0)
      (Set.range (fun i ↦ Away.mk G hr 1 (v i) (by simpa using hv i))) := by
    rw [b54_away_adjoin_ratios_eq_top G hr v hv hgen]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hratios i
  | algebraMap c => exact hbase c
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | mul x y _ _ hx hy => simp only [map_mul, hx, hy]

include hv in
theorem b54_irrelevant_le_span_generators
    (hgen : Algebra.adjoin (G 0) (Set.range v) = ⊤) :
    (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range v) := by
  intro x hx
  have hx0 : GradedRing.projZeroRingHom G x = 0 := by
    change x ∈ HomogeneousIdeal.irrelevant G at hx
    simpa [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      GradedRing.projZeroRingHom_apply] using hx
  suffices x - GradedRing.projZeroRingHom G x ∈ Ideal.span (Set.range v) by
    simpa [hx0] using this
  clear hx hx0
  have hmem : x ∈ Algebra.adjoin (G 0) (Set.range v) := by rw [hgen]; trivial
  induction hmem using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_ne G (hv i) one_ne_zero,
      sub_zero]
    exact Ideal.subset_span (Set.mem_range_self i)
  | algebraMap c =>
    have hc : GradedRing.projZeroRingHom G (algebraMap (G 0) A c) = algebraMap (G 0) A c :=
      DirectSum.decompose_of_mem_same G c.property
    rw [hc, sub_self]
    exact Ideal.zero_mem _
  | add x y _ _ hx hy =>
    simpa only [map_add, add_sub_add_comm] using Ideal.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    convert Ideal.add_mem _ (Ideal.mul_mem_left _ x hy)
      (Ideal.mul_mem_right (GradedRing.projZeroRingHom G y) _ hx) using 1
    rw [map_mul]
    ring

end HodgeLean.Foundations.Program

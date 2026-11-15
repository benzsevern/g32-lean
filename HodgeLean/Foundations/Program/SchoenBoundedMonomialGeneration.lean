import HodgeLean.Foundations.Program.SchoenHighDegreeComponents

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A homogeneous piece is generated over degree zero by the finite family of bounded monomials of its weight. -/
theorem s2_homogeneous_mem_adjoin_boundedMonomials {A ι : Type} [CommRing A] [Fintype ι]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A) (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) (hv : ∀ i, v i ∈ 𝒜 (d i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (M : ℕ)
    {x : A} (hx : x ∈ 𝒜 M) :
    x ∈ Algebra.adjoin (𝒜 0) (Set.range
      (fun a : {a : ι → Fin (M + 1) // ∑ i, (a i).val * d i = M} =>
        ∏ i, v i ^ (a.val i).val)) := by
  classical
  let Q := Algebra.adjoin (𝒜 0) (Set.range
    (fun a : {a : ι → Fin (M + 1) // ∑ i, (a i).val * d i = M} =>
      ∏ i, v i ^ (a.val i).val))
  suffices ∀ a : A, (DirectSum.decompose 𝒜 a M : A) ∈ Q by
    simpa only [DirectSum.decompose_of_mem_same 𝒜 hx] using this x
  intro a
  have ha : a ∈ Submodule.span (𝒜 0) (Submonoid.closure (Set.range v)) := by
    rw [← Algebra.adjoin_eq_span, hgen]
    trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, rfl⟩ := Submonoid.exists_of_mem_closure_range _ _ ha
    have hmon := SetLike.prod_pow_mem_graded 𝒜 d v b (F := Finset.univ) (fun i _ => hv i)
    by_cases hdeg : ∑ i, b i * d i = M
    · rw [DirectSum.decompose_of_mem_same 𝒜 (by simpa only [smul_eq_mul, hdeg] using hmon)]
      have hbound : ∀ i, b i < M + 1 := by
        intro i
        have hi : b i * d i ≤ ∑ j, b j * d j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (b j * d j)) (Finset.mem_univ i)
        rw [hdeg] at hi
        have hdi := hd i
        nlinarith
      exact Algebra.subset_adjoin ⟨⟨fun i => ⟨b i, hbound i⟩, hdeg⟩, rfl⟩
    · rw [DirectSum.decompose_of_mem_ne 𝒜 hmon (by simpa only [smul_eq_mul] using hdeg)]
      exact Q.zero_mem
  | zero =>
    change GradedRing.proj 𝒜 M 0 ∈ Q
    rw [map_zero]
    exact Q.zero_mem
  | add a b ha hb ia ib =>
    change GradedRing.proj 𝒜 M (a + b) ∈ Q
    rw [map_add]
    exact Q.add_mem ia ib
  | smul r a ha ia =>
    change (DirectSum.decompose 𝒜 (r.val * a) M : A) ∈ Q
    rw [DirectSum.coe_decompose_mul_of_left_mem_zero 𝒜 r.property]
    exact Q.mul_mem (Q.algebraMap_mem r) ia

end HodgeLean.Foundations.Program

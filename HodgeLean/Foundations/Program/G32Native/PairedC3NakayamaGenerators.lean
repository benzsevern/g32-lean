import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Local generators retaining a prescribed minimal equation -/

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- A prescribed nonzero class in the residue fibre of a finite local module
lifts to a generating family containing the prescribed element itself.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 2.8. -/
theorem paired_c3_generators_containing
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (t : M) (ht : t ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) :
    ∃ (s : Set (M ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)))
      (b : Module.Basis s (R ⧸ IsLocalRing.maximalIdeal R)
        (M ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)))
      (c : s → M) (j : s),
      c j = t ∧ (∀ i, (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ
        (c i) = b i) ∧ Submodule.span R (Set.range c) = ⊤ := by
  classical
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let N := IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)
  let q := N.mkQ
  have hqt : q t ≠ 0 := by
    exact fun h => ht ((Submodule.Quotient.mk_eq_zero _).mp h)
  have hs : LinearIndepOn (R ⧸ IsLocalRing.maximalIdeal R) id ({q t} : Set (M ⧸ N)) :=
    .singleton hqt
  let s := hs.extend (Set.subset_univ _)
  let b := Module.Basis.extend hs
  let j : s := ⟨q t, hs.subset_extend _ (Set.mem_singleton _)⟩
  let c : s → M := fun i => if i = j then t else (N.mkQ_surjective (b i)).choose
  have hc (i : s) : q (c i) = b i := by
    by_cases hi : i = j
    · subst i
      simp only [c, if_pos rfl]
      exact (Module.Basis.extend_apply_self hs j).symm
    · simp only [c, if_neg hi]
      exact (N.mkQ_surjective (b i)).choose_spec
  refine ⟨s, b, c, j, by simp only [c, if_pos rfl], hc, ?_⟩
  apply IsLocalRing.map_mkQ_eq_top.mp
  rw [Submodule.map_span, ← Set.range_comp]
  have hcb : q ∘ c = b := funext hc
  rw [hcb]
  rw [← Submodule.restrictScalars_span R (R ⧸ IsLocalRing.maximalIdeal R)
    Ideal.Quotient.mk_surjective, b.span_eq]
  rfl

#print axioms paired_c3_generators_containing
end HodgeLean.Foundations.Program.G32Native

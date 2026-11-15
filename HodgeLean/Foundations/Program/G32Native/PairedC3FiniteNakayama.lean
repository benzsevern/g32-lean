import HodgeLean.Foundations.Program.G32Native.PairedC3NakayamaGenerators

/-! # Rank-controlled local generators with a prescribed first element -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- Nakayama generators can be indexed by the exact residue-fibre dimension
and ordered so that the prescribed minimal element is first.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 2.8. -/
theorem paired_c3_finite_generators_first
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (t : M) (ht : t ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
    (n : ℕ) (hdim : Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
      (M ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) = n + 1) :
    ∃ (c : Fin (n + 1) → M)
      (b : Module.Basis (Fin (n + 1)) (R ⧸ IsLocalRing.maximalIdeal R)
        (M ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))),
      c 0 = t ∧ (∀ i, (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ
        (c i) = b i) ∧ Submodule.span R (Set.range c) = ⊤ := by
  classical
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let N := IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)
  letI : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (M ⧸ N) :=
    Module.Finite.of_restrictScalars_finite R _ _
  obtain ⟨s, b, c, j, hj, hc, hspan⟩ := paired_c3_generators_containing t ht
  let bfin := Module.finBasisOfFinrankEq (R ⧸ IsLocalRing.maximalIdeal R) (M ⧸ N) hdim
  let e := b.indexEquiv bfin
  let e' := e.trans (Equiv.swap (e j) 0)
  let c' : Fin (n + 1) → M := c ∘ e'.symm
  refine ⟨c', b.reindex e', ?_, ?_, ?_⟩
  · change c (e'.symm 0) = t
    have he : e'.symm 0 = j := by simp [e']
    rw [he, hj]
  · intro i
    simpa only [c', Function.comp_apply, Module.Basis.reindex_apply] using hc (e'.symm i)
  · have hr : Set.range c' = Set.range c := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e'.symm i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e' i, by simp only [c', Function.comp_apply, Equiv.symm_apply_apply]⟩
    rw [hr, hspan]

#print axioms paired_c3_finite_generators_first
end HodgeLean.Foundations.Program.G32Native

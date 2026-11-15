import HodgeLean.Foundations.Program.G32Native.RegularQuotientParameters

/-! Simultaneous parameters for a finite family of principal branch ideals. -/
noncomputable section
set_option maxHeartbeats 400000
open IsLocalRing
namespace HodgeLean.Foundations.Program

/-- Principal branches with regular joint quotient and expected codimension use distinct parameters. -/
theorem g32l4_principal_family_parameters
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι → Ideal R) (f : ι → R)
    (hprincipal : ∀ i, I i = Ideal.span {f i}) (hproper : ∀ i, I i ≠ ⊤)
    [IsRegularLocalRing (R ⧸ Finset.univ.sup I)]
    (hcodim : ringKrullDim (R ⧸ Finset.univ.sup I) + Fintype.card ι = ringKrullDim R) :
    ∃ (n : ℕ) (z : Fin n → R) (c : ι ↪ Fin n),
      IsRegularSystemOfParameters z ∧ ∀ i, I i = Ideal.span {z (c i)} := by
  classical
  have hfI : ∀ i, f i ∈ I i := by
    intro i
    rw [hprincipal i]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hf : ∀ i, f i ∈ maximalIdeal R :=
    fun i => le_maximalIdeal (hproper i) (hfI i)
  have hgen : Ideal.span (Set.range f) = Finset.univ.sup I := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (Finset.le_sup (f := I) (Finset.mem_univ i)) (hfI i)
    · apply Finset.sup_le
      intro i _
      rw [hprincipal i]
      apply Ideal.span_le.mpr
      exact Set.singleton_subset_iff.mpr (Ideal.subset_span (Set.mem_range_self i))
  obtain ⟨n, z, c, hz, heq⟩ :=
    g32l4_regular_quotient_labelled_parameters (Finset.univ.sup I) f hf hgen hcodim
  refine ⟨n, z, c, hz, ?_⟩
  intro i
  rw [heq i]
  exact hprincipal i

end HodgeLean.Foundations.Program

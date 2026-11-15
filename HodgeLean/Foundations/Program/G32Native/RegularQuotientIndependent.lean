import HodgeLean.Foundations.Program.G32Native.CotangentSpans
import HodgeLean.Ported.Hironaka.Algebra.Local.QuotientParameters

/-! Minimal labelled equations of a regular quotient are independent cotangent classes. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open IsLocalRing
namespace HodgeLean.Foundations.Program

/-- A generating family with the dimension-difference cardinality is independent modulo the square. -/
theorem g32l4_regular_quotient_equations_independent
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (I : Ideal R) [IsRegularLocalRing (R ⧸ I)]
    {ι : Type*} [Fintype ι] (f : ι → R)
    (hf : ∀ i, f i ∈ maximalIdeal R)
    (hgen : Ideal.span (Set.range f) = I)
    (hcodim : ringKrullDim (R ⧸ I) + Fintype.card ι = ringKrullDim R) :
    LinearIndependent (ResidueField R)
      (fun i => (maximalIdeal R).toCotangent ⟨f i, hf i⟩) := by
  classical
  obtain ⟨n, c, z, hcn, hn, hm, hIz⟩ :=
    IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt I
  have hdim := ringKrullDim_quotient_span_image_lt z hm hn hcn
  rw [← hIz] at hdim
  obtain ⟨q, hq⟩ := exists_ringKrullDim_eq_natCast (R ⧸ I)
  have hqc : q + c = n := by
    rw [hq, ← hn] at hdim
    exact_mod_cast hdim
  have hqi : q + Fintype.card ι = n := by
    rw [hq, ← hn] at hcodim
    exact_mod_cast hcodim
  have hcard : Fintype.card ι = c := by omega
  let g : Fin c → R := fun j => z (Fin.castLE hcn j)
  have hg : ∀ j, g j ∈ maximalIdeal R :=
    fun j => x_mem_maximalIdeal_of_span_eq z hm (Fin.castLE hcn j)
  have hIg : I = Ideal.span (Set.range g) := by
    rw [hIz]
    congr 1
    ext a
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j.val, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.castLE hcn j, j.isLt, rfl⟩
  obtain ⟨b, hb⟩ := exists_basis_cotangentSpace_of_span_eq z hm hn
  have hli : LinearIndependent (ResidueField R)
      (fun j => (maximalIdeal R).toCotangent ⟨g j, hg j⟩) := by
    have h := b.linearIndependent.comp (Fin.castLE hcn) (Fin.castLE_injective hcn)
    simpa only [Function.comp_def, hb] using h
  have hsp := g32l4_cotangent_span_eq_of_ideal_span_eq f g hf hg (hgen.trans hIg)
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card ι = Module.finrank (ResidueField R)
    (Submodule.span (ResidueField R)
      (Set.range fun i => (maximalIdeal R).toCotangent ⟨f i, hf i⟩))
  rw [hsp, hcard]
  have h := (linearIndependent_iff_card_eq_finrank_span).mp hli
  change Fintype.card (Fin c) = Module.finrank (ResidueField R)
    (Submodule.span (ResidueField R)
      (Set.range fun j => (maximalIdeal R).toCotangent ⟨g j, hg j⟩)) at h
  simpa only [Fintype.card_fin] using h

end HodgeLean.Foundations.Program

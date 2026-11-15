import HodgeLean.Foundations.Program.SchoenCycleAdicEndomorphismCriterion
import HodgeLean.Foundations.Program.SchoenCycleCotangentBasisGenerators

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A maximal-adic local endomorphism whose actual images represent a cotangent basis is bijective.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 2, 7 and 10. -/
theorem s2e_adic_endomorphism_bijective_of_cotangent_basis
    (k R σ : Type*) [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra k R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (ε : R →ₐ[k] k) (f : R →ₐ[k] R)
    (hf : ∀ r ∈ IsLocalRing.maximalIdeal R, f r ∈ IsLocalRing.maximalIdeal R)
    (c : σ → IsLocalRing.maximalIdeal R)
    (b : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent)
    (hb : ∀ i, b i = (IsLocalRing.maximalIdeal R).toCotangent ⟨f (c i).val, hf _ (c i).property⟩) :
    Function.Bijective f := by
  apply s2e_adic_augmented_endomorphism_bijective k R ε f
  apply le_antisymm
  · exact (Ideal.map_le_iff_le_comap).mpr hf
  · have hspan := s2e_cotangent_basis_generates_maximalIdeal k R σ
      (fun i => ⟨f (c i).val, hf _ (c i).property⟩) b hb
    apply hspan.symm.le.trans
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_map_of_mem f.toRingHom (c i).property

#print axioms s2e_adic_endomorphism_bijective_of_cotangent_basis
end HodgeLean.Foundations.Program

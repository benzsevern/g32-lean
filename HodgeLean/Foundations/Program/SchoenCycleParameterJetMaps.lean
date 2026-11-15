import HodgeLean.Foundations.Program.SchoenCycleParameterJetAlgebra

/-! # Maps from finite parameter neighbourhoods to nilpotent algebras -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A map to a nilpotent parameter algebra is determined by the parameter value.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
finite parameter expansions. -/
theorem s2e_parameter_nilpotent_map_ext
    (R A : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    [CommRing A] [Algebra ℂ A] (φ : R →ₐ[ℂ] ℂ) (t : R)
    (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (N : ℕ) (f g : R →ₐ[ℂ] A) (hn : f t ^ N = 0) (he : f t = g t) : f = g := by
  apply AlgHom.ext
  intro r
  obtain ⟨c, hc⟩ := s2e_local_parameter_jet_expansion R φ t ht N r
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hc
  have hgn : g t ^ N = 0 := by rwa [← he]
  have hf := congrArg f hd
  have hg := congrArg g hd
  simp only [map_sub, map_mul, map_pow, hn, zero_mul, sub_eq_zero] at hf
  simp only [map_sub, map_mul, map_pow, hgn, zero_mul, sub_eq_zero] at hg
  rw [hf, hg]
  simp only [map_sum, map_mul, map_pow, f.commutes, g.commutes, he]

/-- Every nilpotent parameter value defines a unique algebra map out of a
regular one-parameter local algebra with complex residue field.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
finite parameter expansions and quotient algebras. -/
theorem s2e_parameter_nilpotent_map_exists_unique
    (R A : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    [CommRing A] [Algebra ℂ A] (φ : R →ₐ[ℂ] ℂ) (t : R)
    (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (hreg : Function.Injective (fun x : R => t * x))
    (N : ℕ) (a : A) (ha : a ^ N = 0) :
    ∃! f : R →ₐ[ℂ] A, f t = a := by
  let I : Ideal (Polynomial ℂ) := Ideal.span {(Polynomial.X ^ N : Polynomial ℂ)}
  let J : Ideal R := Ideal.span {t ^ N}
  let e := s2e_parameter_jet_algEquiv R φ t ht hreg N
  have hk (p : Polynomial ℂ) (hp : p ∈ I) : Polynomial.aeval a p = 0 := by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp only [map_mul, map_pow, Polynomial.aeval_X, ha, zero_mul]
  let ev : Polynomial ℂ ⧸ I →ₐ[ℂ] A := Ideal.Quotient.liftₐ I (Polynomial.aeval a) hk
  let f : R →ₐ[ℂ] A := ev.comp (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ J))
  have he : e.symm (Ideal.Quotient.mk J t) = Ideal.Quotient.mk I Polynomial.X := by
    apply e.injective
    rw [e.apply_symm_apply]
    simpa only [Polynomial.aeval_X] using
      (s2e_parameter_jet_algEquiv_mk R φ t ht hreg N Polynomial.X).symm
  have hf : f t = a := by
    change ev (e.symm (Ideal.Quotient.mk J t)) = a
    rw [he]
    change Polynomial.aeval a Polynomial.X = a
    exact Polynomial.aeval_X a
  refine ⟨f, hf, ?_⟩
  intro g hg
  apply s2e_parameter_nilpotent_map_ext R A φ t ht N g f
  · rwa [hg]
  · exact hg.trans hf.symm

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCycleAdicBaseStabilizer

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- At a prime fixed by the entire finite group, the actual invariant base adic algebra identifies with the full local invariant formal algebra, retaining its canonical values.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_fixed_prime_adic_base_comparison
    (A C G : Type*) [CommRing A] [Algebra ℂ A] [CommRing C] [Algebra A C]
    [IsNoetherianRing C] [Group G] [Fintype G]
    [MulSemiringAction G C] [SMulCommClass G A C] [Algebra.IsInvariant A C G]
    (hinj : Function.Injective (algebraMap A C)) (P : Ideal C) [P.IsMaximal]
    (hfix : ∀ g : G, g • P = P) :
    let Q := P.under A
    let α := MulSemiringAction.toAlgAut G A C
    ∃ (hP : ∀ (g : G) n c, c ∈ P ^ n → α g c ∈ P ^ n)
      (hQ : ∀ n a, a ∈ Q ^ n → algebraMap A C a ∈ P ^ n)
      (E : AdicCompletion Q A ≃ₐ[A]
        (⨅ g : G, AlgHom.equalizer (s2e_adic_algebra_map P P (α g).toAlgHom (hP g))
          (AlgHom.id A (AdicCompletion P C)) : Subalgebra A (AdicCompletion P C))),
      ∀ x, (E x).val = s2e_adic_algebra_map Q P (Algebra.ofId A C) hQ x := by
  let Q := P.under A
  letI : Algebra.IsIntegral A C := Algebra.IsInvariant.isIntegral A C G
  letI : Q.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  letI : P.LiesOver Q := inferInstance
  let α := MulSemiringAction.toAlgAut G A C
  let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
  have hP (g : G) (n : ℕ) (c : C) (hc : c ∈ P ^ n) : α g c ∈ P ^ n := by
    have hh := Ideal.smul_mem_pointwise_smul g c (P ^ n) hc
    rwa [smul_pow', hfix] at hh
  let β (g : G) := s2e_adic_algebra_map P P (α g).toAlgHom (hP g)
  let β₀ (g : MulAction.stabilizer G o) := s2e_adic_algebra_map P P (α g.val).toAlgHom
    (s2e_orbit_ideal_stabilizer_preserves_powers G C P g)
  let K : Subalgebra A (AdicCompletion P C) := ⨅ g : G, AlgHom.equalizer (β g) (AlgHom.id A _)
  let K₀ : Subalgebra A (AdicCompletion P C) :=
    ⨅ g : MulAction.stabilizer G o, AlgHom.equalizer (β₀ g) (AlgHom.id A _)
  have hK : K₀ = K := by
    ext x
    simp only [K₀, K, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    constructor
    · intro hx g
      have hg : g ∈ MulAction.stabilizer G o := by
        change g • o = o
        apply Subtype.ext
        exact hfix g
      exact hx ⟨g, hg⟩
    · intro hx g
      exact hx g.val
  obtain ⟨E₀, hE₀⟩ := s2e_adic_base_stabilizer_comparison A C G hinj Q P
  have hQ (n : ℕ) (a : A) (ha : a ∈ Q ^ n) : algebraMap A C a ∈ P ^ n :=
    (Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr (Ideal.over_def P Q).le) n)
      (s2e_base_map_preserves_extended_ideal_powers Q n a ha)
  refine ⟨hP, hQ, E₀.trans (Subalgebra.equivOfEq K₀ K hK), ?_⟩
  intro x
  exact hE₀ x

#print axioms s2e_fixed_prime_adic_base_comparison
end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCycleFixedPrimeAdicComparison
import HodgeLean.Foundations.Program.SchoenCycleInvariantScalarValues
import HodgeLean.Foundations.Program.SchoenCycleAdicCommonInvariantPullbacks

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual map from the invariant base to the prime stabilizer fixed-function algebra is bijective on the canonical retained adic algebras.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_stabilizer_fixed_function_adic_map_bijective
    (A C G : Type*) [CommRing A] [Algebra ℂ A] [CommRing C] [Algebra A C]
    [IsNoetherianRing C] [Group G] [Fintype G]
    [MulSemiringAction G C] [SMulCommClass G A C] [Algebra.IsInvariant A C G]
    (hinj : Function.Injective (algebraMap A C)) (P : Ideal C) [P.IsMaximal] :
    let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
    let H := MulAction.stabilizer G o
    let S := FixedPoints.subalgebra A C H
    let I := P.under A
    let Q := P.under S
    ∃ h : ∀ n a, a ∈ I ^ n → algebraMap A S a ∈ Q ^ n,
      Function.Bijective (s2e_adic_algebra_map I Q (Algebra.ofId A S) h) := by
  dsimp only
  let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
  let H := MulAction.stabilizer G o
  let S := FixedPoints.subalgebra A C H
  let I := P.under A
  let Q := P.under S
  letI : Algebra.IsIntegral A C := Algebra.IsInvariant.isIntegral A C G
  letI : I.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  letI : P.LiesOver I := inferInstance
  have hfix (g : H) : g • P = P := by
    have hg : g.val • o = o := g.property
    exact congrArg (fun z : MulAction.orbit G P => z.val) hg
  obtain ⟨E, hE⟩ := s2e_adic_base_stabilizer_comparison A C G hinj I P
  letI : Algebra ℂ S := ((algebraMap A S).comp (algebraMap ℂ A)).toAlgebra
  obtain ⟨hP, hQ, F, hF⟩ := s2e_fixed_prime_adic_base_comparison S C H
    (fun _ _ h => Subtype.ext h) P hfix
  let F' := (F.restrictScalars A).trans (s2e_invariant_restrict_scalars_equiv (k := A) _)
  have h : ∀ n a, a ∈ I ^ n → algebraMap A S a ∈ Q ^ n := by
    intro n a ha
    have hle : I.map (algebraMap A S) ≤ Q := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact ha
    exact (Ideal.pow_right_mono hle n)
      (s2e_base_map_preserves_extended_ideal_powers I n a ha)
  refine ⟨h, ?_⟩
  apply s2e_adic_map_bijective_of_common_invariant_pullbacks I Q P
    (Algebra.ofId A S) ((Algebra.ofId S C).restrictScalars A) h hQ _ E F'
  · intro x
    exact hE x
  · intro y
    exact hF y

#print axioms s2e_stabilizer_fixed_function_adic_map_bijective
end HodgeLean.Foundations.Program

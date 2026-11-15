import HodgeLean.Foundations.Program.SchoenCycleInvariantFibreSupport
import HodgeLean.Foundations.Program.SchoenCycleSemilocalAdicProjection

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual invariant fibre factors retain their canonical maps on every formal section.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_invariant_fibre_canonical_factors
    (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (p : Ideal A) [p.IsMaximal] (I : Ideal B) [I.IsPrime] [I.LiesOver p] :
    ∃ (hJI : ∀ Q : MulAction.orbit G I, p.map (algebraMap A B) ≤ Q.val)
      (E : AdicCompletion (p.map (algebraMap A B)) B ≃ₐ[A]
        (∀ Q : MulAction.orbit G I, AdicCompletion Q.val B)),
      ∀ (x : AdicCompletion (p.map (algebraMap A B)) B) (Q : MulAction.orbit G I),
        E x Q = s2e_adic_algebra_map (p.map (algebraMap A B)) Q.val (AlgHom.id A B)
          (fun n b hb => (Ideal.pow_right_mono (hJI Q) n) hb) x := by
  classical
  letI : Fintype (MulAction.orbit G I) := (Finite.finite_mulAction_orbit (M := G) I).fintype
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have hprime (Q : MulAction.orbit G I) : Q.val.IsPrime := by
    obtain ⟨g, hg⟩ := Q.property
    rw [← hg]
    infer_instance
  have hover (Q : MulAction.orbit G I) : Q.val.LiesOver p := by
    obtain ⟨g, hg⟩ := Q.property
    rw [← hg]
    infer_instance
  have hmax (Q : MulAction.orbit G I) : Q.val.IsMaximal := by
    haveI := hprime Q
    haveI := hover Q
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A)
    rw [← Ideal.over_def Q.val p]
    infer_instance
  have hcop : Pairwise (fun Q Q' : MulAction.orbit G I => IsCoprime Q.val Q'.val) := by
    intro Q Q' hne
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact Ideal.IsMaximal.coprime_of_ne (hmax Q) (hmax Q')
      (fun h => hne (Subtype.ext h))
  have hle (Q : MulAction.orbit G I) : p.map (algebraMap A B) ≤ Q.val := by
    rw [Ideal.map_le_iff_le_comap]
    haveI := hover Q
    exact (Ideal.over_def Q.val p).le
  have hcover : ∀ Q : Ideal B, Q.IsPrime → p.map (algebraMap A B) ≤ Q →
      ∃ Q' : MulAction.orbit G I, Q'.val ≤ Q := by
    intro Q hQ hle
    haveI := hQ
    obtain ⟨g, hg⟩ := s2e_invariant_fibre_prime_orbit A B G p I Q hle
    exact ⟨⟨Q, ⟨g, hg.symm⟩⟩, le_rfl⟩

  obtain ⟨E, hE⟩ := s2e_semilocal_adic_factor_projections (k := A)
    (p.map (algebraMap A B)) (fun Q : MulAction.orbit G I => Q.val)
    hcop hle (Ideal.fg_of_isNoetherianRing _) hcover
  exact ⟨hle, E, hE⟩

end HodgeLean.Foundations.Program

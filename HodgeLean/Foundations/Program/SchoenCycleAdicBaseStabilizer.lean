import HodgeLean.Foundations.Program.SchoenCycleInvariantFibreStabilizer
import HodgeLean.Foundations.Program.SchoenCycleAdicInvariantAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual adic base algebra maps isomorphically onto the stabilizer invariants of one formal prime factor.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_adic_base_stabilizer_comparison
    (A B G : Type*) [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Group G] [Fintype G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (hinj : Function.Injective (algebraMap A B))
    (p : Ideal A) [p.IsMaximal] (I : Ideal B) [I.IsPrime] [I.LiesOver p] :
    let α := MulSemiringAction.toAlgAut G A B
    let o : MulAction.orbit G I := ⟨I, MulAction.mem_orbit_self I⟩
    let β (g : MulAction.stabilizer G o) := s2e_adic_algebra_map I I (α g.val).toAlgHom
      (s2e_orbit_ideal_stabilizer_preserves_powers G B I g)
    ∃ F : AdicCompletion p A ≃ₐ[A]
      (⨅ g : MulAction.stabilizer G o, AlgHom.equalizer (β g)
        (AlgHom.id A (AdicCompletion I B)) : Subalgebra A (AdicCompletion I B)),
      ∀ x, (F x).val = s2e_adic_algebra_map p I (Algebra.ofId A B)
        (fun n a ha => (Ideal.pow_right_mono
          (Ideal.map_le_iff_le_comap.mpr (Ideal.over_def I p).le) n)
          (s2e_base_map_preserves_extended_ideal_powers p n a ha)) x := by
  dsimp only
  let J := p.map (algebraMap A B)
  let α := MulSemiringAction.toAlgAut G A B
  have hdescent (b : B) (hb : ∀ g, α g b = b) : ∃ a : A, algebraMap A B a = b :=
    Algebra.IsInvariant.isInvariant b hb
  let C := s2e_adic_invariant_base_algebra_equiv p α hinj hdescent
  obtain ⟨D, hD⟩ := s2e_invariant_fibre_stabilizer_comparison A B G p I
  refine ⟨C.trans D, ?_⟩
  intro x
  rw [AlgEquiv.trans_apply]
  refine (hD (C x)).trans ?_
  change s2e_adic_algebra_map J I (AlgHom.id A B) _
      (s2e_adic_algebra_map p J (Algebra.ofId A B)
        (s2e_base_map_preserves_extended_ideal_powers p) x) = _
  apply AdicCompletion.ext
  intro n
  change Ideal.quotientMapₐ (I ^ n • ⊤ : Ideal B) (AlgHom.id A B) _
      (Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal B) (Algebra.ofId A B) _ (x.val n)) =
    Ideal.quotientMapₐ (I ^ n • ⊤ : Ideal B) (Algebra.ofId A B) _ (x.val n)
  refine Quotient.inductionOn' (x.val n) (fun a => ?_)
  rfl

end HodgeLean.Foundations.Program

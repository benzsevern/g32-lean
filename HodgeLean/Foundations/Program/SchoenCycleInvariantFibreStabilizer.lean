import HodgeLean.Foundations.Program.SchoenCycleInvariantFibreCanonicalFactors
import HodgeLean.Foundations.Program.SchoenCycleFormalOrbitInvariants
import HodgeLean.Foundations.Program.SchoenCycleOrbitIdealPowers
import HodgeLean.Foundations.Program.SchoenCycleAdicExtendedPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Invariants in the actual extended maximal-fibre adic algebra identify with invariants of the retained prime's formal factor under its actual stabilizer action.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_invariant_fibre_stabilizer_comparison
    (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (p : Ideal A) [p.IsMaximal] (I : Ideal B) [I.IsPrime] [I.LiesOver p] :
    let J := p.map (algebraMap A B)
    let α := MulSemiringAction.toAlgAut G A B
    let a := s2e_adic_group_algebra_action J α
      (fun g => s2e_linear_preserves_extended_ideal_powers p (α g).toLinearMap)
    let o : MulAction.orbit G I := ⟨I, MulAction.mem_orbit_self I⟩
    let β (g : MulAction.stabilizer G o) := s2e_adic_algebra_map I I (α g.val).toAlgHom
      (s2e_orbit_ideal_stabilizer_preserves_powers G B I g)
    ∃ F : (⨅ g : G, AlgHom.equalizer (a g).toAlgHom
        (AlgHom.id A (AdicCompletion J B)) : Subalgebra A (AdicCompletion J B)) ≃ₐ[A]
      (⨅ g : MulAction.stabilizer G o, AlgHom.equalizer (β g)
        (AlgHom.id A (AdicCompletion I B)) : Subalgebra A (AdicCompletion I B)),
      ∀ v, (F v).val = s2e_adic_algebra_map J I (AlgHom.id A B)
        (fun n b hb => (Ideal.pow_right_mono
          (Ideal.map_le_iff_le_comap.mpr (Ideal.over_def I p).le) n) hb) v.val := by
  dsimp only
  let J := p.map (algebraMap A B)
  let α := MulSemiringAction.toAlgAut G A B
  let o : MulAction.orbit G I := ⟨I, MulAction.mem_orbit_self I⟩
  let hJ := fun g => s2e_linear_preserves_extended_ideal_powers p (α g).toLinearMap
  obtain ⟨hJI, E, hE⟩ := s2e_invariant_fibre_canonical_factors A B G p I
  have hI (g : G) (Q : MulAction.orbit G I) (n : ℕ) (b : B)
      (hb : b ∈ Q.val ^ n) : α g b ∈ (g • Q).val ^ n := by
    change g • b ∈ (g • Q.val) ^ n
    rw [← smul_pow']
    exact Ideal.smul_mem_pointwise_smul g b (Q.val ^ n) hb
  have htrans (Q : MulAction.orbit G I) : ∃ g : G, g • o = Q := by
    obtain ⟨g, hg⟩ := Q.property
    exact ⟨g, Subtype.ext hg⟩
  obtain ⟨F, hF⟩ := s2e_formal_orbit_stabilizer_invariants J
    (fun Q : MulAction.orbit G I => Q.val) hJI α hJ hI E hE o htrans
  refine ⟨F, ?_⟩
  intro v
  exact (hF v).trans (hE v.val o)

end HodgeLean.Foundations.Program

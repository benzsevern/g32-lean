import HodgeLean.Foundations.Program.SchoenCycleAdicCotangentGeneration
import HodgeLean.Foundations.Program.SchoenCycleAdicStalkMap

/-! # Transporting adic approximations to original finite jets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An adic approximation to an exact lift induces an approximation in the
original target ring to the same ideal order.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
compatibility of induced adic maps with finite quotient evaluations. -/
theorem s2e_adic_approximation_transport
    {R S : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [CommRing S]
    (J : Ideal S) (f : R →+* S) (hf : (IsLocalRing.maximalIdeal R).map f ≤ J)
    (c : AdicCompletion (IsLocalRing.maximalIdeal R) R) (r : S)
    (hc : s2e_adic_ring_map _ J f hf c = AdicCompletion.of J S r)
    (d : R) (N : ℕ)
    (hd : algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) d - c ∈
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ N) :
    f d - r ∈ J ^ N := by
  have he := (s2e_local_adic_mem_maximalIdeal_pow_iff_eval _ N).mp hd
  rw [map_sub, sub_eq_zero] at he
  have ht := congrArg (s2e_adic_quotient_ring_map _ J f hf N) he
  rw [← s2e_adic_ring_map_eval _ J f hf N c, hc, AdicCompletion.evalₐ_of] at ht
  change Ideal.Quotient.mk (J ^ N) (f d) = Ideal.Quotient.mk (J ^ N) r at ht
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ht

#print axioms s2e_adic_approximation_transport
/-- Approximation to an exact adic stalk lift preserves the same order in the
actual upstairs stalk after pullback.
Source: Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_adic_stalkMap_approximation_transport
    {X Y : Scheme} (f : X ⟶ Y) (p : X)
    [IsNoetherianRing (Y.presheaf.stalk (f p))]
    (c : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f p)))
      (Y.presheaf.stalk (f p))) (r : X.presheaf.stalk p)
    (hc : s2e_adic_stalkMap f p c =
      AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) _ r)
    (d : Y.presheaf.stalk (f p)) (N : ℕ)
    (hd : algebraMap (Y.presheaf.stalk (f p))
      (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f p)))
        (Y.presheaf.stalk (f p))) d - c ∈
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f p)))
        (Y.presheaf.stalk (f p))) ^ N) :
    (f.stalkMap p).hom d - r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ N := by
  exact s2e_adic_approximation_transport _ (f.stalkMap p).hom
    (IsLocalRing.map_maximalIdeal_le (f.stalkMap p).hom) c r hc d N hd

#print axioms s2e_adic_stalkMap_approximation_transport
end HodgeLean.Foundations.Program

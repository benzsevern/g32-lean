import HodgeLean.Foundations.Program.SchoenCycleAdicRingMaps
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # Locality of induced adic maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A local map of Noetherian local rings induces a local map of their
maximal-ideal adic rings.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Mathlib, AdicCompletion.maximalIdeal_eq_map. -/
theorem s2e_adic_ring_map_isLocalHom
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (f : R →+* S) [IsLocalHom f] :
    IsLocalHom (s2e_adic_ring_map (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S)
      f (IsLocalRing.map_maximalIdeal_le f)) := by
  let F := s2e_adic_ring_map (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S)
    f (IsLocalRing.map_maximalIdeal_le f)
  have hc : F.comp (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) =
      (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)).comp f := by
    apply RingHom.ext
    intro r
    exact s2e_adic_ring_map_of _ _ f _ r
  apply ((IsLocalRing.local_hom_TFAE F).out 1 3).mpr
  rw [AdicCompletion.maximalIdeal_eq_map, AdicCompletion.maximalIdeal_eq_map,
    Ideal.map_map, hc, ← Ideal.map_map]
  exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le f)

#print axioms s2e_adic_ring_map_isLocalHom
end HodgeLean.Foundations.Program

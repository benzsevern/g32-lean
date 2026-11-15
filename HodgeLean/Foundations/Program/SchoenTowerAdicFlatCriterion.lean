import HodgeLean.Foundations.Program.SchoenTowerFlatDescent
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Unramified.LocalRing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- An isomorphism of the actual local adic rings over the source makes the original map flat. -/
theorem s2t_flat_of_localAdicAlgEquiv {R S : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    (e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[R]
      AdicCompletion (IsLocalRing.maximalIdeal S) S) : Module.Flat R S := by
  let T := AdicCompletion (IsLocalRing.maximalIdeal S) S
  letI : Module.FaithfullyFlat S T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : Module.Flat R T := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  exact s2t_flat_of_flat_faithfullyFlat (T := T)

/-- A local adic algebra isomorphism forces equality of the extended maximal ideals. -/
theorem s2t_map_maximalIdeal_of_localAdicAlgEquiv {R S : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    (e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[R]
      AdicCompletion (IsLocalRing.maximalIdeal S) S) :
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S := by
  let U := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let T := AdicCompletion (IsLocalRing.maximalIdeal S) S
  letI : Module.FaithfullyFlat S T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hcomm : e.toRingHom.comp (algebraMap R U) = algebraMap R T := by
    apply RingHom.ext
    intro r
    exact e.commutes r
  have hmax : (IsLocalRing.maximalIdeal U).map e.toRingHom = IsLocalRing.maximalIdeal T :=
    IsLocalRing.eq_maximalIdeal ((Ideal.isMaximal_map_iff_of_bijective
      (f := e.toRingHom) e.bijective).mpr inferInstance)
  apply Ideal.map_injective_of_faithfullyFlat (B := T)
  calc
    ((IsLocalRing.maximalIdeal R).map (algebraMap R S)).map (algebraMap S T) =
        (IsLocalRing.maximalIdeal R).map (algebraMap R T) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S T]
    _ = ((IsLocalRing.maximalIdeal R).map (algebraMap R U)).map e.toRingHom := by
      rw [Ideal.map_map, hcomm]
    _ = (IsLocalRing.maximalIdeal U).map e.toRingHom := by
      rw [← AdicCompletion.maximalIdeal_eq_map]
    _ = IsLocalRing.maximalIdeal T := hmax
    _ = (IsLocalRing.maximalIdeal S).map (algebraMap S T) :=
      AdicCompletion.maximalIdeal_eq_map

/-- The local adic comparison and separable residue fields give formal unramifiedness. -/
theorem s2t_unramified_of_localAdicAlgEquiv {R S : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
    (e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[R]
      AdicCompletion (IsLocalRing.maximalIdeal S) S) :
    Algebra.FormallyUnramified R S := by
  exact Algebra.FormallyUnramified.of_map_maximalIdeal
    (s2t_map_maximalIdeal_of_localAdicAlgEquiv e)

end HodgeLean.Foundations.Program

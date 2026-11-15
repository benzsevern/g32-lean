import HodgeLean.Foundations.Program.SchoenTransferQ3TangentialParameters
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! Actual tangential parameters on an unreduced local support. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open IsLocalRing
namespace HodgeLean.Foundations.Program

/-- Parameters generating the reduced support maximal ideal generate the
unreduced support maximal ideal modulo its actual nilradical. -/
theorem s4_q3_parameters_generate_mod_nilradical
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : R →+* A) (b : A →+* B) (hb : Function.Surjective b)
    (hker : RingHom.ker b = nilradical A) (rs : List R)
    (hgen : Ideal.ofList (rs.map (b.comp f)) = maximalIdeal B) :
    Ideal.ofList (rs.map f) ⊔ nilradical A = maximalIdeal A := by
  letI : IsLocalHom b := IsLocalHom.of_surjective b hb
  have h := congrArg (Ideal.comap b) hgen
  rw [← Ideal.map_ofList, ← Ideal.map_map,
    Ideal.comap_map_of_surjective _ hb, ← RingHom.ker_eq_comap_bot,
    hker, maximalIdeal_comap b] at h
  simpa only [Ideal.map_ofList] using h

/-- The actual reduction map preserves the dimension of the unreduced
support stalk. -/
theorem s4_q3_dimension_of_nilradical_kernel
    {A B : Type*} [CommRing A] [CommRing B]
    (b : A →+* B) (hb : Function.Surjective b)
    (hker : RingHom.ker b = nilradical A) :
    ringKrullDim A = ringKrullDim B := by
  let e := (Ideal.primeSpectrumOrderIsoZeroLocusOfSurj b hb hker).trans
    ((Set.orderIsoOfEq _ _ (PrimeSpectrum.zeroLocus_nilradical (R := A))).trans
      OrderIso.Set.univ)
  exact Order.krullDim_eq_of_orderIso e.symm

end HodgeLean.Foundations.Program

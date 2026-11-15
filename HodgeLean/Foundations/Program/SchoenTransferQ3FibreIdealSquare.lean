import HodgeLean.Adapters.NormalConeB4aGysinSliceEquiv
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! Fibre ideals in a surjective square of actual local rings. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open IsLocalRing
namespace HodgeLean.Foundations.Program

/-- A surjective local square preserves the fibre ideal when the source
restriction kernel already lies in the original fibre ideal. -/
theorem s4_q3_fibre_ideal_comap
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing R']
    (f : R →+* S) (a : R →+* R') (b : S →+* S') (g : R' →+* S')
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (hsquare : b.comp f = g.comp a)
    (hker : RingHom.ker b ≤ (maximalIdeal R).map f) :
    ((maximalIdeal R').map g).comap b = (maximalIdeal R).map f := by
  have hmap : ((maximalIdeal R).map f).map b = (maximalIdeal R').map g := by
    rw [Ideal.map_map, hsquare, ← Ideal.map_map, map_maximalIdeal_of_surjective a ha]
  rw [← hmap, Ideal.comap_map_of_surjective _ hb,
    ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]

/-- A compatible surjective local square has the same point-fibre length
when the restriction kernel is contained in the original fibre ideal. -/
theorem s4_q3_fibre_length_surjective_square
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing R']
    (f : R →+* S) (a : R →+* R') (b : S →+* S') (g : R' →+* S')
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (hsquare : b.comp f = g.comp a)
    (hker : RingHom.ker b ≤ (maximalIdeal R).map f) :
    Module.length S (S ⧸ (maximalIdeal R).map f) =
      Module.length S' (S' ⧸ (maximalIdeal R').map g) := by
  let I := (maximalIdeal R).map f
  let J := (maximalIdeal R').map g
  have hc : J.comap b = I := s4_q3_fibre_ideal_comap f a b g ha hb hsquare hker
  let φ : S ⧸ I →+* S' ⧸ J := Ideal.quotientMap J b hc.ge
  let e : (S ⧸ I) ≃+* (S' ⧸ J) := RingEquiv.ofBijective φ
    ⟨Ideal.quotientMap_injective' hc.le, Ideal.quotientMap_surjective hb⟩
  calc
    Module.length S (S ⧸ I) = Module.length (S ⧸ I) (S ⧸ I) :=
      Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
    _ = Module.length (S' ⧸ J) (S' ⧸ J) := HodgeLean.Adapters.a3b2_length_eq_of_ringEquiv e
    _ = Module.length S' (S' ⧸ J) :=
      (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm

end HodgeLean.Foundations.Program

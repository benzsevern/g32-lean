import HodgeLean.Adapters.NormalConeB4aGysinFiniteRegularOpen
import HodgeLean.Adapters.NormalConeB4aGysinLocalModelLength
import Mathlib.RingTheory.Regular.Flat

noncomputable section
namespace HodgeLean.Adapters

/-- In an étale comparison square, a regular source parameter sequence
gives a free neighborhood of a finite model on the comparison base. -/
theorem a3b4a_gysin_etale_model_free_neighborhood
    {A B S T : Type*} [CommRing A] [CommRing B] [CommRing S] [CommRing T]
    [Algebra A B] [Algebra A S] [Algebra A T] [Algebra B T] [Algebra S T]
    [IsScalarTower A B T] [IsScalarTower A S T]
    [Algebra.Etale A B] [Algebra.Etale S T]
    [IsNoetherianRing B] [Module.Finite B T]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [IsLocalRing (P.Fiber T)]
    (r : Ideal T) [r.IsPrime] [r.LiesOver P]
    (xs : List A) (hspan : Ideal.ofList xs = p)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime (r.under S))
      (xs.map (algebraMap A (Localization.AtPrime (r.under S))))) :
    ∃ f : B, f ∉ P ∧ Module.Free (Localization.Away f) (LocalizedModule.Away f T) := by
  let q := r.under S
  let Sq := Localization.AtPrime q
  let Tr := Localization.AtPrime r
  let BP := Localization.AtPrime P
  letI : Algebra Sq Tr := Localization.AtPrime.algebraOfLiesOver q r
  letI : Algebra BP Tr := Localization.AtPrime.algebraOfLiesOver P r
  haveI : IsScalarTower A Sq Tr := IsScalarTower.to₁₃₄ A S Sq Tr
  haveI : IsScalarTower A BP Tr := IsScalarTower.to₁₃₄ A B BP Tr
  haveI : Module.Flat Sq Tr := inferInstance
  let ys := xs.map (algebraMap A BP)
  have hys : Ideal.ofList ys = IsLocalRing.maximalIdeal BP := by
    rw [← Ideal.map_ofList, hspan, a3b4a_gysin_etale_base_prime_ideal p P,
      Localization.AtPrime.map_eq_maximalIdeal]
  have hTreg : RingTheory.Sequence.IsWeaklyRegular Tr (xs.map (algebraMap A Tr)) := by
    have h := hreg.of_flat (S := Tr)
    simpa only [List.map_map, Function.comp_def, ← IsScalarTower.algebraMap_apply] using h
  have hysreg : RingTheory.Sequence.IsWeaklyRegular Tr ys := by
    apply (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff Tr Tr ys).mp
    simpa only [ys, List.map_map, Function.comp_def, ← IsScalarTower.algebraMap_apply] using hTreg
  obtain ⟨f, hf, hfree, _⟩ :=
    a3b4a_gysin_finite_model_free_neighborhood P r ys hys hysreg
  exact ⟨f, hf, hfree⟩

end HodgeLean.Adapters

import HodgeLean.Adapters.NormalConeB4aGysinRegularExactModel
import HodgeLean.Adapters.NormalConeB4aGysinFlatSourceOpen

noncomputable section
namespace HodgeLean.Adapters

/-- Regular base parameters at a quasi-finite source point give a
principal source neighborhood flat over the original base. -/
theorem a3b4a_gysin_exists_flat_source_of_regular_parameters
    {A S : Type} [CommRing A] [IsNoetherianRing A] [CommRing S] [Algebra A S]
    [Algebra.FiniteType A S]
    (p : Ideal A) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.QuasiFiniteAt A q]
    (xs : List A) (hspan : Ideal.ofList xs = p)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime q)
      (xs.map (algebraMap A (Localization.AtPrime q)))) :
    ∃ f : S, f ∉ q ∧ Module.Flat A (Localization.Away f) := by
  obtain ⟨B, T, _, _, _, _, _, _, _, _, _, _, _, _, P, _, _, _, r, _, _, hr, _⟩ :=
    a3b4a_gysin_exists_exact_model_of_regular_parameters p q xs hspan hreg
  haveI : Module.Flat A T := Module.Flat.trans A B T
  letI : r.LiesOver q := ⟨hr.symm⟩
  exact a3b4a_gysin_flat_source_neighborhood_of_etale_model (T := T) q r

end HodgeLean.Adapters

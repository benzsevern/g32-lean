import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Ideal.GoingDown
import HodgeLean.Adapters.NormalConeB4aGysinFlatDescent
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

noncomputable section
namespace HodgeLean.Adapters

/-- An étale source model that is flat over the original base gives a
principal flat neighborhood of every point in its image. -/
theorem a3b4a_gysin_flat_source_neighborhood_of_etale_model
    {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
    [Algebra.Etale S T] [Module.Flat A T]
    (q : Ideal S) [q.IsPrime] (r : Ideal T) [r.IsPrime] [r.LiesOver q] :
    ∃ f : S, f ∉ q ∧ Module.Flat A (Localization.Away f) := by
  let π := PrimeSpectrum.comap (algebraMap S T)
  have ho : IsOpen (Set.range π) :=
    (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := S) (S := T)).isOpen_range
  have hq : (⟨q, inferInstance⟩ : PrimeSpectrum S) ∈ Set.range π := by
    refine ⟨⟨r, inferInstance⟩, ?_⟩
    exact PrimeSpectrum.ext (r.over_def q).symm
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hfq, hsub⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hq ho
  let U := Localization.Away f
  let M := Algebra.algebraMapSubmonoid T (Submonoid.powers f)
  let V := Localization M
  haveI : IsScalarTower A U V := IsScalarTower.to₁₃₄ A S U V
  haveI : Module.Flat A V := Module.Flat.trans A T V
  haveI : Module.Flat S V := Module.Flat.trans S T V
  haveI : Module.Flat U V :=
    (Module.flat_iff_of_isLocalization U (Submonoid.powers f) V).mpr inferInstance
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap U V)) := by
    intro J
    have hfJ : f ∉ J.asIdeal.under S :=
      J.asIdeal.notMem_of_isUnit (IsLocalization.Away.algebraMap_isUnit f)
    obtain ⟨r', hr'⟩ := hsub (show
      (⟨J.asIdeal.under S, inferInstance⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.basicOpen f from hfJ)
    have hr'S : r'.asIdeal.under S = J.asIdeal.under S := congrArg PrimeSpectrum.asIdeal hr'
    have hd : Disjoint (M : Set T) r'.asIdeal := by
      rw [show M = Submonoid.powers (algebraMap S T f) from Algebra.algebraMapSubmonoid_powers f]
      apply (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr
      intro hmem
      apply hfJ
      rw [← hr'S]
      exact hmem
    let rV := r'.asIdeal.map (algebraMap T V)
    haveI : rV.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M V r'.asIdeal inferInstance hd
    haveI : rV.LiesOver r'.asIdeal := IsLocalization.liesOver_map_of_isPrime_disjoint M V hd
    refine ⟨⟨rV, inferInstance⟩, ?_⟩
    apply PrimeSpectrum.localization_comap_injective U (Submonoid.powers f)
    apply PrimeSpectrum.ext
    change (rV.under U).under S = J.asIdeal.under S
    rw [Ideal.under_under, ← Ideal.under_under (A := S) (B := T),
      ← rV.over_def r'.asIdeal, hr'S]
  haveI : Module.FaithfullyFlat U V := Module.FaithfullyFlat.of_comap_surjective hsurj
  exact ⟨f, hfq, a3b4a_gysin_flat_of_faithfullyFlat_source (T := V)⟩

end HodgeLean.Adapters

import HodgeLean.Foundations.Program.SchoenTowerL1aIdealDenominators
import HodgeLean.Foundations.Program.SchoenTowerPointJets
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Principal ideal neighborhoods retaining finite rational support

A local principal equation at one point, nonzero at the remaining support,
spreads to one principal neighborhood of the entire finite support.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A local principal ideal comparison at one point extends over a principal neighborhood of finite support when its equation is nonzero at the other points.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10 and Chapter 3, finite generation and localization. -/
theorem s2v_l1a_principal_ideal_neighborhood_of_point_localization
    {K A ι : Type*} [Field K] [CommRing A] [Algebra K A] [Finite ι]
    (φ : ι → A →ₐ[K] K) (hinj : Function.Injective φ) (i₀ : ι)
    (I : Ideal A) (hI : I.FG) (g : A) (hg : g ∈ I)
    (hzero : ∀ i, i ≠ i₀ → φ i g ≠ 0)
    (hlocal : letI : (RingHom.ker (φ i₀).toRingHom).IsPrime := RingHom.ker_isPrime _
      I.map (algebraMap A (Localization.AtPrime (RingHom.ker (φ i₀).toRingHom))) ≤
        (Ideal.span {g}).map (algebraMap A (Localization.AtPrime (RingHom.ker (φ i₀).toRingHom)))) :
    ∃ d : A, (∀ i, φ i d = 1) ∧
      I.map (algebraMap A (Localization.Away d)) =
        Ideal.span {algebraMap A (Localization.Away d) g} := by
  classical
  let m := RingHom.ker (φ i₀).toRingHom
  letI : m.IsPrime := RingHom.ker_isPrime _
  obtain ⟨s, hs, hsI⟩ := s2v_l1a_finite_ideal_localization_denominator
    (A := Localization.AtPrime m) m.primeCompl I (Ideal.span {g}) hI hlocal
  have hφs : φ i₀ s ≠ 0 := hs
  let J : Ideal A := Ideal.span {g}
  let H : Ideal A := J.colon (I : Set A)
  have hsH : s ∈ H := Submodule.mem_colon.mpr hsI
  have hgH : g ∈ H := by
    apply Submodule.mem_colon.mpr
    intro x hx
    exact J.mul_mem_right x (Ideal.subset_span (Set.mem_singleton g))
  let r (i : ι) := if i = i₀ then s else g
  have hr (i : ι) : φ i (r i) ≠ 0 := by
    dsimp [r]
    split_ifs with hi
    · subst i; exact hφs
    · exact hzero i hi
  obtain ⟨d, hd, hvalues⟩ := s2t_unit_value_in_span φ hinj r hr
  have hdH : d ∈ H := (Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    dsimp [r]
    split_ifs <;> assumption) : Ideal.span (Set.range r) ≤ H) hd
  refine ⟨d, hvalues, ?_⟩
  suffices I.map (algebraMap A (Localization.Away d)) =
      (Ideal.span {g}).map (algebraMap A (Localization.Away d)) by
    simpa only [Ideal.map_span, Set.image_singleton] using this
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hdx := Ideal.mem_map_of_mem (algebraMap A (Localization.Away d)) ((Submodule.mem_colon.mp hdH) x hx)
    rw [smul_eq_mul, map_mul] at hdx
    exact (Ideal.unit_mul_mem_iff_mem _
      (IsLocalization.map_units (Localization.Away d) ⟨d, Submonoid.mem_powers d⟩)).mp hdx
  · exact Ideal.map_mono ((Ideal.span_singleton_le_iff_mem I).mpr hg)

end HodgeLean.Foundations.Program

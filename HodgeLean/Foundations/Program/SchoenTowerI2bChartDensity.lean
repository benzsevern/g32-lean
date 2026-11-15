import HodgeLean.Foundations.Program.SchoenTowerI2bBlowupChartRegular
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! Density on retained divisor charts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The principal open of a regular element is dense in the prime spectrum.
Source: injectivity of localization and the kernel description of spectral image density. -/
theorem s2v_i2b_regular_basicOpen_dense
    {R : Type*} [CommRing R] (v : R)
    (hv : Function.Injective (fun a : R => v * a)) :
    Dense (PrimeSpectrum.basicOpen v : Set (PrimeSpectrum R)) := by
  let L := Localization.Away v
  have hreg : IsRegular v := ⟨hv, IsLeftRegular.right_of_commute (fun _ => Commute.all _ _) hv⟩
  have hinj : Function.Injective (algebraMap R L) := by
    apply (IsLocalization.injective_iff_isRegular (Submonoid.powers v)).mpr
    intro c
    obtain ⟨n, hn⟩ := c.property
    rw [← hn]
    exact hreg.pow n
  have hd : DenseRange (PrimeSpectrum.comap (algebraMap R L)) := by
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R L)).mpr
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap R L)).mp hinj]
    exact bot_le
  rw [DenseRange, PrimeSpectrum.localization_away_comap_range L v] at hd
  exact hd

/-- Saturation identifies a divisor support with the closure away from the denominator.
Source: density in the quotient spectrum and continuity of the quotient spectral map. -/
theorem s2v_i2b_saturated_divisor_density
    {R : Type*} [CommRing R] (I : Ideal R) (v : R)
    (hv : ∀ a : R, v * a ∈ I → a ∈ I) :
    closure (PrimeSpectrum.zeroLocus (I : Set R) ∩
      (PrimeSpectrum.basicOpen v : Set (PrimeSpectrum R))) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  let q := Ideal.Quotient.mk I
  let f := PrimeSpectrum.comap q
  have hrange : Set.range f = PrimeSpectrum.zeroLocus (I : Set R) := by
    simpa only [f, q, Ideal.mk_ker] using
      range_comap_of_surjective (R ⧸ I) q Ideal.Quotient.mk_surjective
  apply Set.Subset.antisymm
  · exact closure_minimal Set.inter_subset_left (PrimeSpectrum.isClosed_zeroLocus _)
  · intro x hx
    obtain ⟨y, rfl⟩ := hrange.symm ▸ hx
    have hd := s2v_i2b_regular_basicOpen_dense (q v)
      (s2v_i2b_quotient_regular_of_saturated I v hv)
    have hcl : f y ∈ closure (f '' (PrimeSpectrum.basicOpen (q v) : Set _)) :=
      image_closure_subset_closure_image (PrimeSpectrum.continuous_comap q)
        ⟨y, hd y, rfl⟩
    apply closure_mono (s := f '' (PrimeSpectrum.basicOpen (q v) : Set _)) ?_ hcl
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hrange ▸ Set.mem_range_self z, ?_⟩
    exact hz

/-- Saturation descends through a surjective presentation whose kernel lies in the ideal.
Source: the comap-map identity for surjective ring homomorphisms. -/
theorem s2v_i2b_saturation_of_surjective
    {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A)
    (hf : Function.Surjective f) (I : Ideal R) (hker : RingHom.ker f ≤ I)
    (v : R) (hv : ∀ a : R, v * a ∈ I → a ∈ I) :
    ∀ a : A, f v * a ∈ Ideal.map f I → a ∈ Ideal.map f I := by
  intro a ha
  obtain ⟨a, rfl⟩ := hf a
  have hcomap : Ideal.comap f (Ideal.map f I) = I := by
    rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  have hmem : v * a ∈ Ideal.comap f (Ideal.map f I) := by
    simpa only [Ideal.mem_comap, map_mul] using ha
  rw [hcomap] at hmem
  exact Ideal.mem_map_of_mem f (hv a hmem)

end HodgeLean.Foundations.Program

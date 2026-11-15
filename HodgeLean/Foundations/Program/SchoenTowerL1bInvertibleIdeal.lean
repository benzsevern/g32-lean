import HodgeLean.Foundations.Program.SchoenTowerL1bChartAlgebra
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program

/-- In a trivialization of a two-generated invertible ideal, the two coefficients generate one. -/
theorem s2v_l1b_invertible_ideal_coefficients {R : Type*} [CommRing R]
    (I : Ideal R) (u v : R) (hu : u ∈ I) (hv : v ∈ I)
    (hI : I = Ideal.span {u, v}) (e : I ≃ₗ[R] R) :
    Ideal.span {e ⟨u, hu⟩, e ⟨v, hv⟩} = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.mem_span_pair.mpr
  have hw : (e.symm 1).val ∈ Ideal.span {u, v} := by
    rw [← hI]
    exact (e.symm 1).property
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hw
  have heq : a • (⟨u, hu⟩ : I) + b • (⟨v, hv⟩ : I) = e.symm 1 := by
    apply Subtype.ext
    exact hab
  refine ⟨a, b, ?_⟩
  have h := congrArg e heq
  simpa only [map_add, map_smul, e.apply_symm_apply, smul_eq_mul] using h

/-- The two coefficient basic opens cover the spectrum of a trivializing ring. -/
theorem s2v_l1b_invertible_ideal_basicOpen_cover {R : Type*} [CommRing R]
    (I : Ideal R) (u v : R) (hu : u ∈ I) (hv : v ∈ I)
    (hI : I = Ideal.span {u, v}) (e : I ≃ₗ[R] R) :
    PrimeSpectrum.basicOpen (e ⟨u, hu⟩) ⊔ PrimeSpectrum.basicOpen (e ⟨v, hv⟩) = ⊤ := by
  have h := PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr
    (s2v_l1b_invertible_ideal_coefficients I u v hu hv hI e)
  simpa only [iSup_insert, iSup_singleton] using h

/-- A unit coefficient in an ideal trivialization gives the unique chart ratio. -/
theorem s2v_l1b_invertible_ideal_ratio {R : Type*} [CommRing R]
    (I : Ideal R) (u v : R) (hu : u ∈ I) (hv : v ∈ I)
    (e : I ≃ₗ[R] R) (hvunit : IsUnit (e ⟨v, hv⟩)) :
    ∃! s : R, u = s * v := by
  let ui : I := ⟨u, hu⟩
  let vi : I := ⟨v, hv⟩
  obtain ⟨w, hw⟩ := hvunit
  let s : R := e ui * ↑w⁻¹
  have hs : s * e vi = e ui := by
    change (e ui * ↑w⁻¹) * e vi = e ui
    rw [← hw, mul_assoc, Units.inv_mul, mul_one]
  have hsI : ui = s • vi := by
    apply e.injective
    rw [map_smul, smul_eq_mul]
    exact hs.symm
  refine ⟨s, congrArg Subtype.val hsI, ?_⟩
  intro t ht
  have htI : ui = t • vi := Subtype.ext ht
  have htc : e ui = t * e vi := by
    rw [htI, map_smul, smul_eq_mul]
  apply (show IsUnit (e vi) from ⟨w, hw⟩).mul_right_cancel
  exact htc.symm.trans hs.symm

/-- A generator with unit trivialization coefficient permits cancellation in the ambient ring. -/
theorem s2v_l1b_invertible_ideal_cancel {R : Type*} [CommRing R]
    (I : Ideal R) (v : R) (hv : v ∈ I) (e : I ≃ₗ[R] R)
    (hvunit : IsUnit (e ⟨v, hv⟩)) {a b : R} (hab : a * v = b * v) : a = b := by
  have hI : a • (⟨v, hv⟩ : I) = b • (⟨v, hv⟩ : I) := Subtype.ext hab
  have hc := congrArg e hI
  simp only [map_smul, smul_eq_mul] at hc
  exact hvunit.mul_right_cancel hc

/-- A unit coefficient in the pulled back ideal supplies the map to the polynomial chart. -/
theorem s2v_l1b_invertible_ideal_chart_map {R A : Type*} [CommRing R] [CommRing A]
    (u v : R) (f : R →+* A) (I : Ideal A)
    (hu : f u ∈ I) (hv : f v ∈ I) (e : I ≃ₗ[A] A)
    (hvunit : IsUnit (e ⟨f v, hv⟩)) :
    ∃ s : A, f u = s * f v ∧
      ∃! φ : s2v_L1bChart u v →+* A,
        φ.comp (Ideal.Quotient.mk (Ideal.span
          {Polynomial.C u - Polynomial.X * Polynomial.C v})) = Polynomial.eval₂RingHom f s := by
  obtain ⟨s, hs, _⟩ := s2v_l1b_invertible_ideal_ratio I (f u) (f v) hu hv e hvunit
  exact ⟨s, hs, s2v_l1b_chart_lift u v f s hs⟩

/-- The two ratios are reciprocal wherever the second ideal coefficient is a unit. -/
theorem s2v_l1b_invertible_ideal_overlap {R : Type*} [CommRing R]
    (I : Ideal R) (u v : R) (hv : v ∈ I) (e : I ≃ₗ[R] R)
    (hvunit : IsUnit (e ⟨v, hv⟩)) (s t : R)
    (hs : u = s * v) (ht : v = t * u) : s * t = 1 := by
  apply s2v_l1b_invertible_ideal_cancel I v hv e hvunit
  rw [mul_comm s t, mul_assoc, ← hs, ← ht, one_mul]

end HodgeLean.Foundations.Program

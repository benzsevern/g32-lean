import HodgeLean.Foundations.Program.SchoenTowerL1aPreProofs
import Mathlib.RingTheory.Flat.TorsionFree

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A flat map from a domain to a nonzero ring is injective. -/
theorem s2v_l1b_divisor_flat_injective
    {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [Nontrivial A]
    (f : R →+* A) (hf : f.Flat) : Function.Injective f := by
  letI := f.toAlgebra
  haveI : Module.Flat R A := hf
  exact FaithfulSMul.algebraMap_injective R A

/-- Each coordinate of an etale polynomial chart is nonzero. -/
theorem s2v_l1b_divisor_etale_coordinate_ne_zero
    {R A J : Type*} [CommRing R] [IsDomain R] [CommRing A] [Nontrivial A]
    (c : R →+* A) (z : J → A) (hEt : (MvPolynomial.eval₂Hom c z).Etale) (j : J) :
    z j ≠ 0 := by
  have hh := (s2v_l1b_divisor_flat_injective (MvPolynomial.eval₂Hom c z)
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hEt).1).ne
    (MvPolynomial.X_ne_zero j)
  simpa only [MvPolynomial.eval₂Hom_X', map_zero] using hh

end HodgeLean.Foundations.Program

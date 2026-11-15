import HodgeLean.Foundations.Program.SchoenTowerL1bReducedChartTransform
import HodgeLean.Foundations.Program.SchoenTowerL1bReducedBaseChange
import HodgeLean.Foundations.Program.SchoenTowerL1bFlatRegularPair
import HodgeLean.Foundations.Program.SchoenTowerL1bCoordinateDivisor
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! Retaining a coordinate divisor across a chart with an exceptional parameter.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A regular quotient parameter misses every minimal component of the principal divisor. -/
theorem s2v_l1b_regular_quotient_avoids_components
    {R : Type*} [CommRing R] (u v : R)
    (hv : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v)) :
    ∀ q ∈ (Ideal.span {u}).minimalPrimes, v ∉ q := by
  intro q hq hvq
  obtain ⟨w, hw, hvw⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hq hvq
  apply hw
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hv.left
  change Ideal.Quotient.mk (Ideal.span {u}) v * Ideal.Quotient.mk (Ideal.span {u}) w =
    Ideal.Quotient.mk (Ideal.span {u}) v * 0
  rw [mul_zero, ← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hvw

/-- A radical principal divisor retains its actual transform ideal when the pulled-back
centre contains a parameter regular modulo that divisor, even on the exceptional locus. -/
theorem s2v_l1b_strictTransform_regular_quotient
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : X.affineOpens) (u v : Γ(X, U))
    (hD : (D.comap f).ideal U = Ideal.span {u})
    (hK : v ∈ (K.comap f).ideal U)
    (hr : (Ideal.span {u}).IsRadical)
    (hv : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v)) :
    (s2c_strictTransform f D K).ideal U = Ideal.span {u} := by
  rw [← hD]
  apply s2v_l1b_strictTransform_ideal_reduced_chart
  · rwa [hD]
  · rw [hD]
    intro q hq hle
    exact s2v_l1b_regular_quotient_avoids_components u v hv q hq (hle hK)

/-- An etale polynomial coordinate generates a radical ideal. -/
theorem s2v_l1b_etale_coordinate_radical
    {k R σ : Type*} [CommRing k] [IsDomain k] [CommRing R]
    (f : k →+* R) (z : σ → R) (het : (MvPolynomial.eval₂Hom f z).Etale)
    (i : σ) : (Ideal.span {z i}).IsRadical := by
  classical
  letI : Algebra (MvPolynomial σ k) R := (MvPolynomial.eval₂Hom f z).toAlgebra
  letI : Algebra.Etale (MvPolynomial σ k) R := het
  let I : Ideal (MvPolynomial σ k) := Ideal.span {MvPolynomial.X i}
  letI : I.IsPrime := s2v_l1b_coordinate_ideal_prime i
  have H := s2v_l1b_etale_map_prime_radical (A := R) I
  simpa only [I, Ideal.map_span, Set.image_singleton, RingHom.algebraMap_toAlgebra,
    MvPolynomial.eval₂Hom_X'] using H

/-- Etale chart coordinates identify an untouched actual transform without excluding
points where the exceptional coordinate vanishes. -/
theorem s2v_l1b_strictTransform_etale_coordinate
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : X.affineOpens) {k σ : Type*} [CommRing k] [IsDomain k]
    (c : k →+* Γ(X, U)) (z : σ → Γ(X, U))
    (het : (MvPolynomial.eval₂Hom c z).Etale) (i j : σ) (hij : i ≠ j)
    (hD : (D.comap f).ideal U = Ideal.span {z i})
    (hK : z j ∈ (K.comap f).ideal U) :
    (s2c_strictTransform f D K).ideal U = Ideal.span {z i} := by
  exact s2v_l1b_strictTransform_regular_quotient f D K U (z i) (z j) hD hK
    (s2v_l1b_etale_coordinate_radical c z het i)
    (s2v_l1b_etale_coordinate_pair c z het j i hij.symm).2

end HodgeLean.Foundations.Program

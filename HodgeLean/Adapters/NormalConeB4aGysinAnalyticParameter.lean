import HodgeLean.Adapters.NormalConeB4aGysinModelPoint
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Etale

/-! # Analytic lifts of parameters through the comparison base -/

noncomputable section
namespace HodgeLean.Adapters
open AlgebraicGeometry ComplexAlgHom

/-- An étale comparison base has a local analytic parameter lift through
its chosen complex point, preserving every polynomial base function. -/
theorem a3b4a_gysin_exists_analytic_parameter_lift
    {n : ℕ} (T : Type) [CommRing T] [Algebra ℂ T]
    [Algebra (complexPolynomialRing n) T]
    [IsScalarTower ℂ (complexPolynomialRing n) T]
    [Algebra.Etale (complexPolynomialRing n) T] (u : T →ₐ[ℂ] ℂ) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧
      mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom T u) ∈ U ∧
      ∃ F : (Fin n → ℂ) → (T →ₐ[ℂ] ℂ), ContinuousOn F U ∧
        F (mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom T u)) = u ∧
        (∀ z ∈ U, etaleBaseAlgHom T (F z) = (mvPolynomialAlgHomHomeomorph n).symm z) ∧
        (∀ r : T, AnalyticOnNhd ℂ (fun z => F z r) U) := by
  let e := etaleAlgHomProjectionChart (n := n) T u
  have hu : u ∈ e.source := mem_etaleAlgHomProjectionChart_source T u
  have hbase : e u = mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom T u) :=
    etaleAlgHomProjectionChart_apply_of_mem T u u hu
  refine ⟨e.target, e.open_target, hbase ▸ e.map_source hu, e.symm,
    e.continuousOn_symm, ?_, ?_, ?_⟩
  · rw [← hbase]
    exact e.left_inv hu
  · intro z hz
    apply (mvPolynomialAlgHomHomeomorph n).injective
    rw [Homeomorph.apply_symm_apply]
    rw [← etaleAlgHomProjectionChart_apply_of_mem T u (e.symm z) (e.map_target hz)]
    exact e.right_inv hz
  · intro r z hz
    exact analyticAt_etaleAlgHomProjectionChart_symm_apply T u hz r

/-- The prime selected by a complex algebra evaluation varies continuously
from the analytic topology to the Zariski topology. -/
theorem a3b4a_gysin_continuous_evaluation_prime
    (T : Type) [CommRing T] [Algebra ℂ T] :
    Continuous (fun u : T →ₐ[ℂ] ℂ =>
      (⟨RingHom.ker u, RingHom.ker_isPrime u⟩ : PrimeSpectrum T)) := by
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨r, rfl⟩
  change IsOpen {u : T →ₐ[ℂ] ℂ | u r ≠ 0}
  exact isOpen_ne_fun (ComplexPoint.continuous_affineAlgebraHom_apply T r) continuous_const

end HodgeLean.Adapters

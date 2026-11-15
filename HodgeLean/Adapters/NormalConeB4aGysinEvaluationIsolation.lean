import HodgeLean.Adapters.NormalConeB4aGysinEvaluationKernel
import HodgeLean.Adapters.NormalConeB4aGysinAnalyticParameter
import Mathlib.RingTheory.ZariskisMainTheorem

noncomputable section
namespace HodgeLean.Adapters

/-- A quasi-finite point is isolated in its complex evaluation fibre. -/
theorem a3b4a_gysin_quasiFinite_evaluation_isolated
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Algebra.FiniteType B T]
    (q : Ideal T) [q.IsPrime] [Algebra.QuasiFiniteAt B q]
    (w₀ : T →ₐ[ℂ] ℂ) (hw₀ : RingHom.ker w₀ = q) :
    ∃ N : Set (T →ₐ[ℂ] ℂ), IsOpen N ∧ w₀ ∈ N ∧
      ∀ w ∈ N, w.comp (IsScalarTower.toAlgHom ℂ B T) =
        w₀.comp (IsScalarTower.toAlgHom ℂ B T) → w = w₀ := by
  let x : PrimeSpectrum T := ⟨q, inferInstance⟩
  let P := PrimeSpectrum.comap (algebraMap B T) ⁻¹' {x.comap (algebraMap B T)}
  have H : IsOpen (X := P) {⟨x, rfl⟩} :=
    (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber (R := B) x).mp inferInstance
  obtain ⟨V, hV, hEq⟩ := isOpen_induced_iff.mp H
  have hxV : x ∈ V := by
    have hx : (⟨x, rfl⟩ : P) ∈ Subtype.val ⁻¹' V := by
      rw [hEq]
      exact Set.mem_singleton _
    exact hx
  let κ := fun w : T →ₐ[ℂ] ℂ =>
    (⟨RingHom.ker w, RingHom.ker_isPrime w⟩ : PrimeSpectrum T)
  have hκ₀ : κ w₀ = x := PrimeSpectrum.ext hw₀
  refine ⟨κ ⁻¹' V, hV.preimage (a3b4a_gysin_continuous_evaluation_prime T), ?_, ?_⟩
  · change κ w₀ ∈ V
    rw [hκ₀]
    exact hxV
  · intro w hw hbase
    let y := κ w
    have hybase : y.comap (algebraMap B T) = x.comap (algebraMap B T) := by
      apply PrimeSpectrum.ext
      change (RingHom.ker w.toRingHom).comap (algebraMap B T) = q.comap (algebraMap B T)
      rw [← hw₀, RingHom.comap_ker]
      exact congrArg (fun f : B →ₐ[ℂ] ℂ => RingHom.ker f.toRingHom) hbase
    have hy : (⟨y, hybase⟩ : P) ∈ ({⟨x, rfl⟩} : Set P) := by
      rw [← hEq]
      exact hw
    have hxy : y = x := congrArg Subtype.val (Set.mem_singleton_iff.mp hy)
    apply a3b4a_gysin_evaluation_eq_of_ker_eq
    exact (congrArg PrimeSpectrum.asIdeal hxy).trans hw₀.symm

end HodgeLean.Adapters

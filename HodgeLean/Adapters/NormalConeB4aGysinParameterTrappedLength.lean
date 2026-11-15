import HodgeLean.Adapters.NormalConeB4aGysinFiniteTrappedLength

noncomputable section
namespace HodgeLean.Adapters
open AlgebraicGeometry ComplexAlgHom

/-- An etale parameter lift gives exact length conservation in every
prescribed neighborhood of a marked local finite fibre. -/
theorem a3b4a_gysin_etale_parameter_length_trapping
    {n : ℕ} {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra (complexPolynomialRing n) B] [IsScalarTower ℂ (complexPolynomialRing n) B]
    [Algebra.Etale (complexPolynomialRing n) B]
    [Algebra B T] [IsScalarTower ℂ B T]
    [Module.FinitePresentation B T] [Module.Flat B T]
    (p : Ideal B) [p.IsPrime] (u : B →ₐ[ℂ] ℂ) (hu : RingHom.ker u = p)
    [IsLocalRing (p.Fiber T)]
    (hzero : mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom B u) = 0)
    (w₀ : T →ₐ[ℂ] ℂ) (hw₀ : w₀.comp (IsScalarTower.toAlgHom ℂ B T) = u) :
    ∃ (U : Set (Fin n → ℂ)), IsOpen U ∧ 0 ∈ U ∧
      ∃ F : (Fin n → ℂ) → (B →ₐ[ℂ] ℂ), ContinuousOn F U ∧ F 0 = u ∧
        (∀ a ∈ U, etaleBaseAlgHom B (F a) = (mvPolynomialAlgHomHomeomorph n).symm a) ∧
        ∀ N : Set (T →ₐ[ℂ] ℂ), IsOpen N → w₀ ∈ N →
          ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ → a ∈ U ∧
            ∃ P : Finset (T →ₐ[ℂ] ℂ),
              (∀ w, w ∈ P ↔ w ∈ N ∧ w.comp (IsScalarTower.toAlgHom ℂ B T) = F a) ∧
              ∑ w ∈ P, a3b4a_gysin_evaluationSliceLength (F a) w =
                Module.length (p.Fiber T) (p.Fiber T) := by
  obtain ⟨U, hU, huU, F, hF, hFu, hbase, _⟩ :=
    a3b4a_gysin_exists_analytic_parameter_lift (n := n) B u
  rw [hzero] at huU hFu
  refine ⟨U, hU, huU, F, hF, hFu, hbase, ?_⟩
  intro N hN hwN
  letI : Algebra.FiniteType ℂ B :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℂ (complexPolynomialRing n))
      (inferInstance : Algebra.FiniteType (complexPolynomialRing n) B)
  obtain ⟨V, hV, huV, hlength⟩ :=
    a3b4a_gysin_finite_evaluation_length_trapping p u hu w₀ hw₀ N hN hwN
  have hW : IsOpen (U ∩ F ⁻¹' V) := hF.isOpen_inter_preimage hU hV
  have h0W : (0 : Fin n → ℂ) ∈ U ∩ F ⁻¹' V := by
    refine ⟨huU, ?_⟩
    change F 0 ∈ V
    rw [hFu]
    exact huV
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hW 0 h0W
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  have hav : a ∈ U ∩ F ⁻¹' V := hball (by
    simpa only [Metric.mem_ball, dist_zero_right] using ha)
  exact ⟨hav.1, hlength (F a) hav.2⟩

end HodgeLean.Adapters

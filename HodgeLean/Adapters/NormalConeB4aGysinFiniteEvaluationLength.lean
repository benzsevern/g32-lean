import HodgeLean.Adapters.NormalConeB4aGysinFiniteEvaluationFibre
import HodgeLean.Adapters.NormalConeB4aGysinAnalyticLength

noncomputable section
namespace HodgeLean.Adapters

/-- The full local parameter quotient length at a complex algebra evaluation. -/
def a3b4a_gysin_evaluationSliceLength
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] (u : B →ₐ[ℂ] ℂ) (w : T →ₐ[ℂ] ℂ) : ℕ∞ :=
  letI : (RingHom.ker w).IsPrime := RingHom.ker_isPrime w
  let L := Localization.AtPrime (RingHom.ker w)
  Module.length L (L ⧸ (RingHom.ker u).map (algebraMap B L))

/-- Near a local special fibre of a finite flat algebra, complex fibre
points carry a conserved sum of full source parameter-quotient lengths. -/
theorem a3b4a_gysin_finite_evaluation_length_neighborhood
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T]
    [Module.FinitePresentation B T] [Module.Flat B T]
    (p : Ideal B) [p.IsPrime] (u : B →ₐ[ℂ] ℂ) (hu : RingHom.ker u = p)
    [IsLocalRing (p.Fiber T)] :
    ∃ V : Set (B →ₐ[ℂ] ℂ), IsOpen V ∧ u ∈ V ∧
      ∀ v ∈ V, ∃ F : Finset (T →ₐ[ℂ] ℂ),
        (∀ w, w ∈ F ↔ w.comp (IsScalarTower.toAlgHom ℂ B T) = v) ∧
        ∑ w ∈ F, a3b4a_gysin_evaluationSliceLength v w =
          Module.length (p.Fiber T) (p.Fiber T) := by
  classical
  obtain ⟨e, _⟩ := a3b4a_gysin_exists_rational_residue_equiv p u hu
  letI : IsAlgClosed p.ResidueField :=
    IsAlgClosed.of_ringEquiv ℂ p.ResidueField e.symm.toRingEquiv
  obtain ⟨U, hU, hp, hsum⟩ :=
    a3b4a_gysin_local_fibre_length_eq_sum_nearby (A := T) ⟨p, inferInstance⟩
  let κ := fun v : B →ₐ[ℂ] ℂ =>
    (⟨RingHom.ker v, RingHom.ker_isPrime v⟩ : PrimeSpectrum B)
  have hκ := a3b4a_gysin_continuous_evaluation_prime B
  have hκu : κ u = ⟨p, inferInstance⟩ := PrimeSpectrum.ext hu
  refine ⟨κ ⁻¹' U, hU.preimage hκ, ?_, ?_⟩
  · change κ u ∈ U
    rw [hκu]
    exact hp
  · intro v hv
    letI : (RingHom.ker v).IsPrime := RingHom.ker_isPrime v
    obtain ⟨ev, _⟩ := a3b4a_gysin_exists_rational_residue_equiv (RingHom.ker v) v rfl
    letI : IsAlgClosed (RingHom.ker v).ResidueField :=
      IsAlgClosed.of_ringEquiv ℂ (RingHom.ker v).ResidueField ev.symm.toRingEquiv
    have hf := a3b4a_gysin_finite_evaluation_fibre (T := T) v
    let F := hf.toFinset
    let X := {w : T →ₐ[ℂ] ℂ // w.comp (IsScalarTower.toAlgHom ℂ B T) = v}
    let E : F ≃ X := Equiv.subtypeEquivRight (fun w => hf.mem_toFinset)
    letI : Fintype X := Fintype.ofEquiv F E
    refine ⟨F, (fun w => hf.mem_toFinset), ?_⟩
    calc
      ∑ w ∈ F, a3b4a_gysin_evaluationSliceLength v w =
          ∑ w : F, a3b4a_gysin_evaluationSliceLength v w.val :=
        (Finset.sum_coe_sort F _).symm
      _ = ∑ w : X, a3b4a_gysin_evaluationSliceLength v w.val :=
        Equiv.sum_comp E (fun w : X => a3b4a_gysin_evaluationSliceLength v w.val)
      _ = ∑ᶠ w : X, a3b4a_gysin_evaluationSliceLength v w.val :=
        (finsum_eq_sum_of_fintype (fun w : X => a3b4a_gysin_evaluationSliceLength v w.val)).symm
      _ = ∑ᶠ x : PrimeSpectrum ((RingHom.ker v).Fiber T),
          Module.length (Localization.AtPrime x.asIdeal) (Localization.AtPrime x.asIdeal) :=
        a3b4a_gysin_fibre_evaluation_length_sum (T := T) (RingHom.ker v) v rfl
      _ = Module.length (p.Fiber T) (p.Fiber T) := (hsum (κ v) hv).symm

end HodgeLean.Adapters

import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.DeckEvaluationOrbits

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The specified normalization-ring restriction of the original full-order symmetry generates every evaluation fibre. -/
theorem integralClosure_evaluation_retained_orbit
    {k R K L : Type*} [Field k] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra k R] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L]
    (δ : L ≃ₐ[K] L) (hδ : orderOf δ = Module.finrank K L)
    (ρ : integralClosure R L ≃+* integralClosure R L)
    (hρ : ∀ b, (ρ b : L) = δ (b : L))
    (p q : integralClosure R L →+* k)
    (hbase : ∀ r, p (algebraMap R (integralClosure R L) r) =
      q (algebraMap R (integralClosure R L) r))
    (hp : ∀ a : k, p (algebraMap R (integralClosure R L) (algebraMap k R a)) = a)
    (hq : ∀ a : k, q (algebraMap R (integralClosure R L) (algebraMap k R a)) = a) :
    ∃ n : ℕ, ∀ b, p (ρ^[n] b) = q b := by
  letI := IsIntegralClosure.MulSemiringAction R K L (integralClosure R L)
  obtain ⟨n, hn⟩ := integralClosure_evaluation_deck_orbit δ hδ p q hbase hp hq
  have hsemi : Function.Semiconj (fun b : integralClosure R L => (b : L)) ρ δ := hρ
  refine ⟨n, fun b => ?_⟩
  have heq : ρ^[n] b = δ ^ n • b := by
    apply Subtype.ext
    calc
      (ρ^[n] b : L) = δ^[n] (b : L) := hsemi.iterate_right n b
      _ = (δ ^ n) (b : L) := (congrFun (AlgEquiv.coe_pow δ n) (b : L)).symm
      _ = (δ ^ n • b : integralClosure R L) :=
        (algebraMap_galRestrict_apply R (δ ^ n) b).symm
  rw [heq]
  exact hn b

end AlgebraicGeometry.RamifiedNormalization.StageFour

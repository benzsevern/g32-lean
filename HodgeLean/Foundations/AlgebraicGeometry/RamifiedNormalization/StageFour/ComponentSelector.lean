import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.DividedChart

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The gcd quotient of a divided generator is an integral component selector. -/
theorem binomial_component_selector
    {A K : Type} [CommRing A] [Field K] (F : A →+* K)
    (m α : ℕ) (hm : 0 < m) (ε s : A) (hs : F s ≠ 0)
    (w : normalizedChart F)
    (hw : w ^ m = StageTwo.integralCoeff F (ε * s ^ α)) :
    ∃ q : normalizedChart F,
      (q : K) = (w : K) ^ (m / Nat.gcd m α) / F s ^ (α / Nat.gcd m α) ∧
      q ^ Nat.gcd m α = StageTwo.integralCoeff F ε ∧
      w ^ (m / Nat.gcd m α) = q * StageTwo.integralCoeff F s ^ (α / Nat.gcd m α) := by
  let g := Nat.gcd m α
  have hg : 0 < g := Nat.gcd_pos_of_pos_left α hm
  have hmg : m / g * g = m := Nat.div_mul_cancel (Nat.gcd_dvd_left m α)
  have hag : α / g * g = α := Nat.div_mul_cancel (Nat.gcd_dvd_right m α)
  let t : K := (w : K) ^ (m / g) / F s ^ (α / g)
  have hwe : (w : K) ^ m = F ε * F s ^ α := by
    have he := congrArg (fun z : normalizedChart F => (z : K)) hw
    change (w : K) ^ m = F (ε * s ^ α) at he
    simpa only [map_mul, map_pow] using he
  have ht : t ^ g = F ε := by
    dsimp [t]
    rw [div_pow, ← pow_mul, ← pow_mul, hmg, hag, hwe]
    exact mul_div_cancel_right₀ (F ε) (pow_ne_zero α hs)
  have hint : t ∈ normalizedChart F := by
    letI := F.toAlgebra
    change _root_.IsIntegral A t
    apply IsIntegral.of_pow hg
    rw [ht]
    exact isIntegral_algebraMap
  let q : normalizedChart F := ⟨t, hint⟩
  refine ⟨q, rfl, ?_, ?_⟩
  · apply Subtype.ext
    exact ht
  · apply Subtype.ext
    change (w : K) ^ (m / g) = t * F s ^ (α / g)
    exact (div_mul_cancel₀ _ (pow_ne_zero _ hs)).symm

/-- The selector is a unit whenever the divided coefficient is a unit. -/
theorem binomial_component_selector_isUnit
    {A K : Type} [CommRing A] [Field K] (F : A →+* K)
    (g : ℕ) (hg : 0 < g) (ε : A) (hε : IsUnit ε)
    (q : normalizedChart F) (hq : q ^ g = StageTwo.integralCoeff F ε) :
    IsUnit q := by
  apply (isUnit_pow_iff (Nat.ne_of_gt hg)).mp
  rw [hq]
  exact hε.map (StageTwo.integralCoeff F)

/-- All integer powers of a unit of the normalized chart remain integral elements. -/
theorem normalizedChart_unit_zpow
    {A K : Type} [CommRing A] [Field K] (F : A →+* K)
    (q : normalizedChart F) (hq : IsUnit q) (b : ℤ) :
    (q : K) ^ b ∈ normalizedChart F := by
  have hi : (q : K)⁻¹ ∈ normalizedChart F := by
    rcases hq with ⟨u, rfl⟩
    change ((normalizedChart F).subtype (↑u : normalizedChart F))⁻¹ ∈ normalizedChart F
    rw [← map_units_inv (normalizedChart F).subtype u]
    exact (↑u⁻¹ : normalizedChart F).property
  cases b with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using (normalizedChart F).pow_mem q.property n
  | negSucc n =>
    simpa only [zpow_negSucc, inv_pow] using (normalizedChart F).pow_mem hi (n + 1)

/-- Complex evaluations preserve integer powers of integral units. -/
theorem normalizedChart_unit_zpow_eval
    {A K : Type} [CommRing A] [Field K] (F : A →+* K)
    (q b : normalizedChart F) (hq : IsUnit q) (k : ℤ)
    (hb : (b : K) = (q : K) ^ k) (ev : normalizedChart F →+* ℂ) :
    ev b = ev q ^ k := by
  rcases hq with ⟨u, rfl⟩
  let f : (normalizedChart F)ˣ →* K :=
    (normalizedChart F).subtype.toMonoidHom.comp (Units.coeHom _)
  have he : b = (↑(u ^ k) : normalizedChart F) := by
    apply Subtype.ext
    exact hb.trans (f.map_zpow u k).symm
  rw [he]
  exact (ev.toMonoidHom.comp (Units.coeHom _)).map_zpow u k

end AlgebraicGeometry.RamifiedNormalization.StageFour

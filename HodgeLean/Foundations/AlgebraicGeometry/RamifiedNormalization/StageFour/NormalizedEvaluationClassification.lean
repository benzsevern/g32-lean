import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.BinomialCoordinateClassification
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoordinateEigenvalues
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.EvaluationReconstruction

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The original integral binomial equation and retained evaluation action give all labelled branch coordinates from properness, fibre orbits and branch inertia. -/
theorem normalized_binomial_evaluation_homeomorph
    {A K : Type} [CommRing A] [Field K] (F : A →+* K)
    {X : Type*} [TopologicalSpace X] (ev : X → (normalizedChart F →+* ℂ)) (d : X → X)
    (m α : ℕ) (hm : 0 < m) (ε s : A) (hε : IsUnit ε) (hs : F s ≠ 0)
    (w : normalizedChart F) (hw : w ^ m = StageTwo.integralCoeff F (ε * s ^ α))
    (σ : K ≃+* K) (ρ : normalizedChart F ≃+* normalizedChart F)
    (hρ : ∀ b, (ρ b : K) = σ (b : K))
    (c : normalizedChart F) (hc : IsUnit c)
    (hsσ : σ (F s) = F s) (hwσ : σ (w : K) = (c : K) * (w : K))
    (ε₀ ζ : ℂ) (hε₀ : ε₀ ≠ 0) (hζ : IsPrimitiveRoot ζ m)
    (hεev : ∀ x, ev x (StageTwo.integralCoeff F ε) = ε₀)
    (hcev : ∀ x, ev x c = ζ)
    (heval : ∀ x b, ev (d x) b = ev x (ρ b))
    (hcont : ∀ b, Continuous (fun x => ev x b))
    (hproper : IsProperMap (fun x => ev x (StageTwo.integralCoeff F s)))
    (hsurj : Function.Surjective (fun x => ev x (StageTwo.integralCoeff F s)))
    (horbit : ∀ x y, ev x (StageTwo.integralCoeff F s) = ev y (StageTwo.integralCoeff F s) →
      ∃ k : ℕ, d^[k] x = y)
    (hperiod : ∀ x, d^[m] x = x)
    (hinertia : ∀ x, ev x (StageTwo.integralCoeff F s) = 0 → d^[α] x = x)
    (hp : ∀ x, ev (d x) (StageTwo.integralCoeff F s) = ev x (StageTwo.integralCoeff F s)) :
    let g := Nat.gcd m α
    let n := m / g
    let a := α / g
    ∃ (q t : normalizedChart F) (κ : ℂ) (E : X ≃ₜ ZMod g × ℂ),
      (q : K) = (w : K) ^ n / F s ^ a ∧
      (t : K) = F s ^ Nat.gcdA n a * (w : K) ^ Nat.gcdB n a ∧
      κ ^ g = ε₀ ∧ κ ≠ 0 ∧
      (∀ j : ZMod g, (κ * (ζ ^ n) ^ j.val) ^ (-Nat.gcdB n a) ≠ 0) ∧
      ∀ x, ev x q = κ * (ζ ^ n) ^ (E x).1.val ∧ ev x t = (E x).2 ∧
        ev x (StageTwo.integralCoeff F s) =
          (κ * (ζ ^ n) ^ (E x).1.val) ^ (-Nat.gcdB n a) * (E x).2 ^ n := by
  dsimp only
  let g := Nat.gcd m α
  let n := m / g
  let a := α / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left α hm
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m α)) hg
  have hcop : n.Coprime a := Nat.coprime_div_gcd_div_gcd hg
  obtain ⟨q, hqval, hqpow, hwq⟩ := binomial_component_selector F m α hm ε s hs w hw
  have hqu : IsUnit q := binomial_component_selector_isUnit F g hg ε hε q hqpow
  obtain ⟨t, b, htval, hbval, hbu, htpow, hrecon⟩ :=
    binomial_canonical_integral_parameter F n a hn hcop s hs w q hqu hwq
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq ε₀ hg
  have hκ0 : κ ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.ne_of_gt hg)] at hκ
    exact hε₀ hκ.symm
  have hroot (x : X) : ev x q ^ g = κ ^ g := by
    rw [← map_pow, hqpow, hεev, hκ]
  have hreconstruct (x : X) : ev x w = ev x t ^ a * ev x q ^ Nat.gcdA n a :=
    normalized_binomial_evaluation_reconstruction F w q t hqu a (Nat.gcdA n a)
      hrecon.symm (ev x)
  have hpower (x : X) : ev x (StageTwo.integralCoeff F s) =
      ev x q ^ (-Nat.gcdB n a) * ev x t ^ n := by
    have hbeq := normalizedChart_unit_zpow_eval F q b hqu (Nat.gcdB n a) hbval (ev x)
    have he := congrArg (ev x) htpow
    simp only [map_pow, map_mul] at he
    calc
      _ = (ev x b)⁻¹ * ev x t ^ n := by
        rw [he, ← mul_assoc, inv_mul_cancel₀ ((hbu.map (ev x)).ne_zero), one_mul]
      _ = _ := by rw [hbeq, zpow_neg]
  have heigen (x : X) := normalized_binomial_deck_evaluation F σ ρ hρ s w q t c hc
    hsσ hwσ n a (Nat.gcdA n a) (Nat.gcdB n a) hqval htval (ev x)
  have hWstep (x : X) : ev (d x) w = ζ * ev x w := by
    rw [heval, (heigen x).1, hcev]
  have hQstep (x : X) : ev (d x) q = ζ ^ n * ev x q := by
    rw [heval, (heigen x).2.1, hcev]
  have hWeigen : ∀ k x, ev (d^[k] x) w = ζ ^ k * ev x w := by
    intro k
    induction k with
    | zero => intro x; rw [Function.iterate_zero_apply, pow_zero, one_mul]
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', hWstep, ih, pow_succ', mul_assoc]
  have hQeigen : ∀ k x, ev (d^[k] x) q = (ζ ^ n) ^ k * ev x q := by
    intro k
    induction k with
    | zero => intro x; rw [Function.iterate_zero_apply, pow_zero, one_mul]
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', hQstep, ih, pow_succ', mul_assoc]
  have hginertia (x : X) (ht : ev x t = 0) : d^[g] x = x := by
    have hs0 : ev x (StageTwo.integralCoeff F s) = 0 := by
      rw [hpower, ht, zero_pow (Nat.ne_of_gt hn), mul_zero]
    have hpm : Function.IsPeriodicPt d m x := hperiod x
    have hpα : Function.IsPeriodicPt d α x := hinertia x hs0
    exact hpm.gcd hpα
  have hmn : m = g * n := (Nat.mul_div_cancel' (Nat.gcd_dvd_left m α)).symm
  obtain ⟨hk, E, hE⟩ := binomial_orbit_coordinate_homeomorph d
    (fun x => ev x (StageTwo.integralCoeff F s)) (fun x => ev x q) (fun x => ev x t)
    (fun x => ev x w) m g n a hg hn hmn (Nat.gcdA n a) (Nat.gcdB n a) κ ζ hκ0 hζ
    hroot hreconstruct hpower (hcont q) (hcont t) hproper hp hsurj horbit hperiod
    hginertia hWeigen hQeigen
  exact ⟨q, t, κ, E, hqval, htval, hκ, hκ0, hk, hE⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour

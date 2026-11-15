import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.BranchParameter

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The integral branch parameter retains its literal Bezout expression and reconstructs the original generator. -/
theorem binomial_canonical_integral_parameter
    {A K : Type} [CommRing A] [Field K] (F : A →+* K)
    (n a : ℕ) (hn : 0 < n) (hcop : n.Coprime a)
    (s : A) (hs : F s ≠ 0) (w q : normalizedChart F) (hq : IsUnit q)
    (hw : w ^ n = q * StageTwo.integralCoeff F s ^ a) :
    ∃ t b : normalizedChart F,
      (t : K) = F s ^ Nat.gcdA n a * (w : K) ^ Nat.gcdB n a ∧
      (b : K) = (q : K) ^ Nat.gcdB n a ∧ IsUnit b ∧
      t ^ n = b * StageTwo.integralCoeff F s ∧
      (t : K) ^ a * (q : K) ^ Nat.gcdA n a = (w : K) := by
  obtain ⟨t₀, b, hb, hbu, ht₀, heval⟩ :=
    binomial_integral_parameter F n a hn hcop s hs w q hq hw
  have hwe : (w : K) ^ n = (q : K) * F s ^ a :=
    congrArg (fun z : normalizedChart F => (z : K)) hw
  let z : K := F s ^ Nat.gcdA n a * (w : K) ^ Nat.gcdB n a
  have hz : z ^ n = (q : K) ^ Nat.gcdB n a * F s :=
    binomial_bezout_parameter_power n a hcop (F s) (w : K) (q : K) hs hwe
  have hint : z ∈ normalizedChart F := by
    letI := F.toAlgebra
    change _root_.IsIntegral A z
    apply IsIntegral.of_pow hn
    rw [hz, ← hb]
    exact (b * StageTwo.integralCoeff F s).property
  let t : normalizedChart F := ⟨z, hint⟩
  have ht : t ^ n = b * StageTwo.integralCoeff F s := by
    apply Subtype.ext
    exact hz.trans (congrArg (fun c : K => c * F s) hb.symm)
  have hw0 : (w : K) ≠ 0 := by
    intro hw0
    have hq0 : (q : K) ≠ 0 := (hq.map (normalizedChart F).subtype).ne_zero
    have hne := mul_ne_zero hq0 (pow_ne_zero a hs)
    apply hne
    rw [← hwe, hw0, zero_pow (Nat.ne_of_gt hn)]
  exact ⟨t, b, rfl, hb, hbu, ht,
    binomial_bezout_reconstruction n a hcop (F s) (w : K) (q : K) hw0 hwe⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour

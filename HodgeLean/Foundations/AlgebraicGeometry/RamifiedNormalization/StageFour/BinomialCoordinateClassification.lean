import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ContinuousBinomialCoordinates
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.BinomialReturnDivisors
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.PeriodicFibreCardinality
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.PowerProjectionCardinality
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.FibreCardinalityCoordinates
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProperFibreCoordinates

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Canonical binomial evaluations exhaust the labelled complex lines when the original deck orbits, inertia and proper projection are retained. -/
theorem binomial_orbit_coordinate_homeomorph
    {X : Type*} [TopologicalSpace X]
    (d : X → X) (p Q T W : X → ℂ)
    (m g n a : ℕ) (hg : 0 < g) (hn : 0 < n) (hm : m = g * n)
    (A B : ℤ) (κ ζ : ℂ) (hκ : κ ≠ 0)
    (hζ : IsPrimitiveRoot ζ m)
    (hroot : ∀ x, Q x ^ g = κ ^ g)
    (hW : ∀ x, W x = T x ^ a * Q x ^ A)
    (hpower : ∀ x, p x = Q x ^ (-B) * T x ^ n)
    (hQc : Continuous Q) (hTc : Continuous T) (hproper : IsProperMap p)
    (hp : ∀ x, p (d x) = p x) (hsurj : Function.Surjective p)
    (horbit : ∀ x y, p x = p y → ∃ k : ℕ, d^[k] x = y)
    (hperiod : ∀ x, d^[m] x = x)
    (hinertia : ∀ x, T x = 0 → d^[g] x = x)
    (hWeigen : ∀ k x, W (d^[k] x) = ζ ^ k * W x)
    (hQeigen : ∀ k x, Q (d^[k] x) = (ζ ^ n) ^ k * Q x) :
    let k : ZMod g → ℂ := fun j => (κ * (ζ ^ n) ^ j.val) ^ (-B)
    (∀ j, k j ≠ 0) ∧ ∃ E : X ≃ₜ ZMod g × ℂ,
      ∀ x, Q x = κ * (ζ ^ n) ^ (E x).1.val ∧ T x = (E x).2 ∧
        p x = k (E x).1 * (E x).2 ^ n := by
  classical
  letI : NeZero g := ⟨Nat.ne_of_gt hg⟩
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hmpos : 0 < m := by rw [hm]; exact Nat.mul_pos hg hn
  let ξ := ζ ^ n
  have hξ : IsPrimitiveRoot ξ g := IsPrimitiveRoot.pow hmpos hζ (hm.trans (Nat.mul_comm g n))
  have hν : IsPrimitiveRoot (ζ ^ g) n := IsPrimitiveRoot.pow hmpos hζ hm
  let k : ZMod g → ℂ := fun j => (κ * (ζ ^ n) ^ j.val) ^ (-B)
  have hξ0 : ξ ≠ 0 := (hξ.isUnit (Nat.ne_of_gt hg)).ne_zero
  have hk (j : ZMod g) : k j ≠ 0 :=
    zpow_ne_zero _ (mul_ne_zero hκ (pow_ne_zero _ hξ0))
  have hQ (x : X) : Q x ≠ 0 := by
    intro hz
    have he := hroot x
    rw [hz, zero_pow (Nat.ne_of_gt hg)] at he
    exact pow_ne_zero g hκ he.symm
  obtain ⟨f, hf, hcoord, heq⟩ := continuous_binomial_root_coordinates g hg κ ξ hκ hξ
    Q T hroot hQc hTc
  let q : ZMod g × ℂ → ℂ := fun z => k z.1 * z.2 ^ n
  have hprojection (x : X) : q (f x) = p x := by
    rw [hpower x, (hcoord x).1, (hcoord x).2]
  have hbase (x y : X) (hQxy : Q x = Q y) (hTxy : T x = T y) : p x = p y := by
    rw [hpower x, hpower y, hQxy, hTxy]
  have hinjPair := binomial_orbit_coordinates_injective d p Q T W m g a A ζ ξ hζ hξ
    hQ hW hbase horbit hperiod hinertia hWeigen hQeigen
  have hinj : Function.Injective f := by
    intro x y hxy
    exact hinjPair (Prod.ext ((heq x y).mp hxy).1 ((heq x y).mp hxy).2)
  have hzero (x : X) : T x = 0 ↔ p x = 0 := by
    rw [hpower x]
    constructor
    · intro ht
      rw [ht, zero_pow (Nat.ne_of_gt hn), mul_zero]
    · intro hz
      exact eq_zero_of_pow_eq_zero
        ((mul_eq_zero.mp hz).resolve_left (zpow_ne_zero _ (hQ x)))
  let N : ℂ → ℕ := fun b => if b = 0 then g else m
  have hN (b : ℂ) : 0 < N b := by
    dsimp only [N]
    split_ifs
    · exact hg
    · rw [hm]
      exact Nat.mul_pos hg hn
  have hreturn : ∀ x k, d^[k] x = x ↔ N (p x) ∣ k := by
    intro x k
    simpa only [N, hzero x] using
      binomial_coordinate_return_divisor d Q T W m g a A ζ ξ hζ hξ hQ hW
        hperiod hinertia hWeigen hQeigen x k
  have hsource (b : ℂ) := periodic_fibre_cardinality d p N hN hp hsurj horbit hreturn b
  have htarget (b : ℂ) := weighted_power_fibre_cardinality g n hg hn k hk (ζ ^ g) hν b
  letI : ∀ b : ℂ, Finite {z : ZMod g × ℂ // q z = b} := fun b => (htarget b).1
  have hcard (b : ℂ) : Nat.card {x : X // p x = b} =
      Nat.card {z : ZMod g × ℂ // q z = b} := by
    rw [(hsource b).2, (htarget b).2]
    simp only [N, hm]
  have hbij := fibre_coordinates_bijective_of_card f p q hinj hprojection hcard
  have hkc : Continuous k := continuous_of_discreteTopology
  have hqc : Continuous q := (hkc.comp continuous_fst).mul (continuous_snd.pow n)
  let E := properFibreCoordinateHomeomorph f p q hf hqc hproper hprojection hbij
  refine ⟨hk, E, ?_⟩
  intro x
  refine ⟨(hcoord x).1, (hcoord x).2, ?_⟩
  exact (hprojection x).symm

end AlgebraicGeometry.RamifiedNormalization.StageFour

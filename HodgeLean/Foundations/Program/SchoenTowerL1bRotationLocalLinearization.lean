import HodgeLean.Foundations.Program.SchoenTowerL1bRotationTangent

noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Averaging a parameter in the residue kernel retains its zero residue,
also when the tangent character is one. -/
theorem s2v_l1b_rotation_eigenparameter_residue
    {R K : Type*} [CommRing R] [Field K] [CharZero K] [Algebra K R]
    (ι : R →ₐ[K] PowerSeries K) (u : R) (hu : ι u = PowerSeries.X)
    (τ : R →ₐ[K] R) (ζ : K) (hζ : ζ ≠ 0)
    (N : ℕ) (hN : 0 < N) (hζN : ζ ^ N = 1) (hperiod : τ^[N] u = u)
    (hres : ∀ v, PowerSeries.constantCoeff (ι (τ v)) = PowerSeries.constantCoeff (ι v))
    (htan : ∀ v, PowerSeries.coeff 1 (ι (τ v)) = ζ * PowerSeries.coeff 1 (ι v)) :
    ∃ v : R, τ v = algebraMap K R ζ * v ∧
      PowerSeries.constantCoeff (ι v) = 0 ∧ PowerSeries.coeff 1 (ι v) = 1 := by
  let A := ∑ i ∈ Finset.range N,
    (algebraMap K R ζ) ^ (N - 1 - i) * τ^[i] u
  let c : K := ((N : K) * ζ ^ (N - 1))⁻¹
  have hi (i : ℕ) : PowerSeries.constantCoeff (ι (τ^[i] u)) = 0 ∧
      PowerSeries.coeff 1 (ι (τ^[i] u)) = ζ ^ i := by
    induction i with
    | zero => simp only [Function.iterate_zero_apply, hu, PowerSeries.constantCoeff_X,
        PowerSeries.coeff_one_X, pow_zero, and_self]
    | succ i ih =>
      rw [Function.iterate_succ_apply', hres, htan, ih.2, pow_succ']
      exact ⟨ih.1, rfl⟩
  have hc : (N : K) * ζ ^ (N - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)) (pow_ne_zero _ hζ)
  refine ⟨c • A, ?_, ?_, ?_⟩
  · have he := s2v_l1b_rotation_orbit_sum_eigen τ.toRingHom (algebraMap K R ζ) u N
      (τ.commutes ζ) (by rw [← map_pow, hζN, map_one]) hperiod
    change τ A = algebraMap K R ζ * A at he
    simp only [Algebra.smul_def, map_mul, τ.commutes, he]
    ring
  · have hz : PowerSeries.constantCoeff (ι A) = 0 := by
      dsimp [A]
      simp only [map_sum, map_mul, map_pow, ι.commutes]
      apply Finset.sum_eq_zero
      intro i _
      rw [(hi i).1, mul_zero]
    simp only [Algebra.smul_def, map_mul, ι.commutes, PowerSeries.constantCoeff_C, hz, mul_zero]
  · let q : R →ₗ[K] K := (PowerSeries.coeff 1).comp ι.toLinearMap
    have he := s2v_l1b_rotation_orbit_sum_linear τ.toRingHom ζ u N q
      (fun i _ => by change PowerSeries.coeff 1 (ι (τ^[i] u)) = ζ ^ i * PowerSeries.coeff 1 (ι u)
                     rw [(hi i).2, hu, PowerSeries.coeff_one_X, mul_one])
    change q A = (N : K) * (ζ ^ (N - 1) * q u) at he
    change q (c • A) = 1
    rw [map_smul, he]
    change c * ((N : K) * (ζ ^ (N - 1) * PowerSeries.coeff 1 (ι u))) = 1
    rw [hu, PowerSeries.coeff_one_X, mul_one, inv_mul_cancel₀ hc]

/-- A periodic local action has an equivariant parameter expansion for its
actual tangent scalar, including the scalar one. -/
theorem s2v_l1b_rotation_local_linearization
    {R K : Type*} [CommRing R] [Field K] [CharZero K] [Algebra K R]
    (ι : R →ₐ[K] PowerSeries K) (hι : Function.Injective ι)
    [IsLocalHom (PowerSeries.constantCoeff.comp ι.toRingHom)]
    (u : R) (hu : ι u = PowerSeries.X)
    (hker : RingHom.ker (PowerSeries.constantCoeff.comp ι.toRingHom) = Ideal.span {u})
    (τ : R →ₐ[K] R) [IsLocalHom τ.toRingHom]
    (N : ℕ) (hN : 0 < N) (hperiod : τ^[N] u = u) :
    ∃ ψ : R →+* PowerSeries K, Function.Injective ψ ∧
      (∃ v, ψ v = PowerSeries.X) ∧
      (∀ k, ψ (algebraMap K R k) = PowerSeries.C k) ∧
      ∀ v, ψ (τ v) = PowerSeries.rescale (PowerSeries.coeff 1 (ι (τ u))) (ψ v) := by
  let ζ := PowerSeries.coeff 1 (ι (τ u))
  have hc (k : K) : ι (algebraMap K R k) = PowerSeries.C k := ι.commutes k
  have hres := s2v_l1b_rotation_residue_invariant
    (PowerSeries.constantCoeff.comp ι.toRingHom)
    (fun k => by change PowerSeries.constantCoeff (ι (algebraMap K R k)) = k
                 rw [hc, PowerSeries.constantCoeff_C]) τ
  have ht := s2v_l1b_rotation_tangent_scalar ι u hu hker τ hres
  have hζN : ζ ^ N = 1 := s2v_l1b_rotation_tangent_pow ι u hu hker τ hres N hperiod
  have hζ : ζ ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.ne_of_gt hN)] at hζN
    exact zero_ne_one hζN
  obtain ⟨v, heigen, hvzero, hvone⟩ := s2v_l1b_rotation_eigenparameter_residue
    ι u hu τ ζ hζ N hN hζN hperiod hres ht
  have hvlinear : IsUnit (PowerSeries.coeff 1 (ι v)) := hvone.symm ▸ isUnit_one
  have hvker := s2v_l1b_rotation_reparameterized_kernel ι.toRingHom u hu hker v hvzero hvlinear
  obtain ⟨ψ, hψ, hψc, hψv⟩ := s2v_l1b_rotation_expansion_reparameterize
    (algebraMap K R) ι.toRingHom hι hc v hvzero hvlinear
  refine ⟨ψ, hψ, ⟨v, hψv⟩, hψc, ?_⟩
  apply s2v_l1b_rotation_expansion_equivariance (algebraMap K R) ψ hψc
    τ.toRingHom (fun k => τ.commutes k) v hψv ζ heigen
  apply s2v_l1b_rotation_parameter_division (algebraMap K R)
    (PowerSeries.constantCoeff.comp ι.toRingHom) _ v hvker
  intro k
  change PowerSeries.constantCoeff (ι (algebraMap K R k)) = k
  rw [hc, PowerSeries.constantCoeff_C]

/-- A periodic local action with tangent scalar one fixes every stalk element. -/
theorem s2v_l1b_rotation_tangent_one_rigid
    {R K : Type*} [CommRing R] [Field K] [CharZero K] [Algebra K R]
    (ι : R →ₐ[K] PowerSeries K) (hι : Function.Injective ι)
    [IsLocalHom (PowerSeries.constantCoeff.comp ι.toRingHom)]
    (u : R) (hu : ι u = PowerSeries.X)
    (hker : RingHom.ker (PowerSeries.constantCoeff.comp ι.toRingHom) = Ideal.span {u})
    (τ : R →ₐ[K] R) [IsLocalHom τ.toRingHom]
    (N : ℕ) (hN : 0 < N) (hperiod : τ^[N] u = u)
    (ht : PowerSeries.coeff 1 (ι (τ u)) = 1) :
    ∀ v, τ v = v := by
  obtain ⟨ψ, hψ, _, _, he⟩ := s2v_l1b_rotation_local_linearization ι hι u hu hker τ N hN hperiod
  intro v
  apply hψ
  rw [he, ht, PowerSeries.rescale_one, RingHom.id_apply]

end HodgeLean.Foundations.Program

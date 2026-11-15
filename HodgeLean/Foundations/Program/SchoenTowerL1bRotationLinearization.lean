import HodgeLean.Foundations.Program.SchoenTowerL1bRotationAveraging
import HodgeLean.Foundations.Program.SchoenTowerL1bRotationEquivariance
import HodgeLean.Foundations.Program.SchoenTowerL1bRotationReparameterization

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- A finite-order action with a nontrivial tangent character admits an
injective equivariant expansion when an initial parameter expansion and its
principal residue kernel are available. -/
theorem s2v_l1b_rotation_formal_linearization
    {R K : Type*} [CommRing R] [Field K] [CharZero K] [Algebra K R]
    (ι : R →ₐ[K] PowerSeries K) (hι : Function.Injective ι)
    [IsLocalHom (PowerSeries.constantCoeff.comp ι.toRingHom)]
    (u : R) (hu : ι u = PowerSeries.X)
    (hker : RingHom.ker (PowerSeries.constantCoeff.comp ι.toRingHom) = Ideal.span {u})
    (τ : R →ₐ[K] R) (N : ℕ) (hN : 0 < N) (hperiod : τ^[N] u = u)
    (ζ : K) (hζ : ζ ≠ 0) (hζone : ζ ≠ 1) (hζN : ζ ^ N = 1)
    (hres : ∀ v, PowerSeries.constantCoeff (ι (τ v)) = PowerSeries.constantCoeff (ι v))
    (htan : ∀ v, PowerSeries.coeff 1 (ι (τ v)) = ζ * PowerSeries.coeff 1 (ι v)) :
    ∃ ψ : R →+* PowerSeries K, Function.Injective ψ ∧
      (∃ v, ψ v = PowerSeries.X) ∧
      (∀ k, ψ (algebraMap K R k) = PowerSeries.C k) ∧
      ∀ v, ψ (τ v) = PowerSeries.rescale ζ (ψ v) := by
  let q : R →ₗ[K] K := (PowerSeries.coeff 1).comp ι.toLinearMap
  obtain ⟨v, heigen, hq⟩ := s2v_l1b_rotation_eigenparameter_of_tangent
    τ.toRingHom (fun k => τ.commutes k) ζ hζ u N hN hζN hperiod q htan
  change τ v = (algebraMap K R ζ) * v at heigen
  have hqv : PowerSeries.coeff 1 (ι v) = 1 := by
    change PowerSeries.coeff 1 (ι v) = PowerSeries.coeff 1 (ι u) at hq
    rwa [hu, PowerSeries.coeff_one_X] at hq
  have hιc (k : K) : ι (algebraMap K R k) = PowerSeries.C k := ι.commutes k
  have hcv : ζ * PowerSeries.constantCoeff (ι v) = PowerSeries.constantCoeff (ι v) := by
    have hh := hres v
    rw [heigen, map_mul, hιc, map_mul, PowerSeries.constantCoeff_C] at hh
    exact hh
  have hvzero : PowerSeries.constantCoeff (ι v) = 0 := by
    have hh : (ζ - 1) * PowerSeries.constantCoeff (ι v) = 0 := by
      rw [sub_mul, one_mul, hcv, sub_self]
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hζone)
  have hvlinear : IsUnit (PowerSeries.coeff 1 (ι v)) := hqv.symm ▸ isUnit_one
  have hvker := s2v_l1b_rotation_reparameterized_kernel ι.toRingHom u hu hker v hvzero hvlinear
  obtain ⟨ψ, hψ, hψc, hψv⟩ := s2v_l1b_rotation_expansion_reparameterize
    (algebraMap K R) ι.toRingHom hι hιc v hvzero hvlinear
  refine ⟨ψ, hψ, ⟨v, hψv⟩, hψc, ?_⟩
  apply s2v_l1b_rotation_expansion_equivariance (algebraMap K R) ψ hψc
    τ.toRingHom (fun k => τ.commutes k) v hψv ζ heigen
  apply s2v_l1b_rotation_parameter_division (algebraMap K R)
    (PowerSeries.constantCoeff.comp ι.toRingHom) _ v hvker
  intro k
  change PowerSeries.constantCoeff (ι (algebraMap K R k)) = k
  rw [hιc, PowerSeries.constantCoeff_C]

end HodgeLean.Foundations.Program

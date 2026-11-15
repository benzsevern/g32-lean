import HodgeLean.Foundations.Program.CurveJacobianAElliptic
import HodgeLean.Foundations.Program.CurveJacobianAPeriods
import HodgeLean.Foundations.Program.CurveJacobianATorusLoops

/-! # Track B3, lane A: the Abel–Jacobi map of the elliptic curve

Every holomorphic form on `ℂ ⧸ (ℤ + iℤ)` is a multiple of `dz`, the `dz`-periods of the period lattice
are Gaussian integers, and with the explicit values of an Abel–Jacobi map based at `0` this shows
that the map is bijective.
-/

noncomputable section

open Manifold Filter Topology
open scoped ContDiff TensorProduct

namespace HodgeLean.Foundations.Program

section Elliptic2

/-- The loop `a` as a `C¹` loop. -/
def b3A_loopA : b3_SmoothLoop b3_EllipticModel b3_Elliptic :=
  ⟨b3_ellipticA, fun t ↦ (b3_ellipticPoint_add_one t 0).1, b3A_ellipticA_contMDiff⟩

/-- The loop `b` as a `C¹` loop. -/
def b3A_loopB : b3_SmoothLoop b3_EllipticModel b3_Elliptic :=
  ⟨b3_ellipticB, fun t ↦ (b3_ellipticPoint_add_one 0 t).2, b3A_ellipticB_contMDiff⟩

/-- Every vector of `(ℂ ⊗ ℤ²) ⧸ F` is `s [e₀] + t [e₁]` with `s, t` real. -/
theorem b3A_quot_eq (w : (ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) :
    w = ((b3A_φ w).re : ℂ) • b3A_e 0 + ((b3A_φ w).im : ℂ) • b3A_e 1 := by
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ b3A_e0_ne_zero).1 b3A_finrank_quot w
  rw [map_smul, b3A_φ_e0, smul_eq_mul, mul_one, b3A_e_one, smul_smul, ← add_smul]
  congr 1
  apply Complex.ext <;> simp

/-- Every point of the elliptic curve is a point with real lattice coordinates. -/
theorem b3A_ellipticPoint_surjective (x : b3_Elliptic) : ∃ s t : ℝ, b3_ellipticPoint s t = x := by
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact ⟨_, _, by rw [b3A_ellipticPoint_eq, ← b3A_quot_eq]⟩

/-- `dz` is nonzero. -/
theorem b3A_dz_ne_zero : b3A_dz ≠ 0 := by
  intro h
  have h1 : b3_pathPeriod _ _ b3_ellipticA b3A_dz = 1 := by
    rw [b3A_ellipticA_eq, b3A_line_pathPeriod, b3A_formFunctional_dz, b3A_φ_e0]
  rw [h] at h1
  simp [b3_pathPeriod, b3_pathIntegral] at h1

/-- Every holomorphic form on the elliptic curve is a multiple of `dz`. -/
theorem b3A_holForm_eq_smul_dz (θ : b3_HolForm b3_EllipticModel b3_Elliptic) :
    ∃ c : ℂ, θ = c • b3A_dz := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ b3A_dz_ne_zero).1
    b3A_elliptic_finrank_holForm θ
  exact ⟨c, hc.symm⟩

/-- On the elliptic curve, a linear functional on `Ω¹` is determined by its value on `dz`. -/
theorem b3A_linearDual_ext {u u' : b3_HolForm b3_EllipticModel b3_Elliptic → ℂ}
    (hu : u ∈ b3_linearDual _ _) (hu' : u' ∈ b3_linearDual _ _) (h : u b3A_dz = u' b3A_dz) :
    u = u' := by
  funext θ
  obtain ⟨c, rfl⟩ := b3A_holForm_eq_smul_dz θ
  rw [b3A_linearDual_smul hu, b3A_linearDual_smul hu', h]

/-- The periods of `dz` on the period lattice are Gaussian integers. -/
theorem b3A_lattice_dz (u : b3_periodLattice b3_EllipticModel b3_Elliptic) :
    ∃ x : Fin 2 → ℤ, (u : b3_HolForm _ _ → ℂ) b3A_dz = (x 0 : ℂ) + Complex.I * (x 1 : ℂ) := by
  obtain ⟨u, hu⟩ := u
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨γ, rfl⟩ := hy
    obtain ⟨x, hx⟩ := b3A_torus_loop_period b2_stdF γ.1 γ.2.2 (by simpa using γ.2.1 0) b3A_dz
    refine ⟨x, ?_⟩
    refine Eq.trans ?_ ((hx.trans (b3A_formFunctional_dz _)).trans (b3A_φ_latticeMap x))
    rfl
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨x, hx⟩ := hy
    obtain ⟨x', hx'⟩ := hz
    refine ⟨x + x', ?_⟩
    simp only [Pi.add_apply, Int.cast_add] at hx hx' ⊢
    rw [hx, hx']
    ring
  | neg y _ hy =>
    obtain ⟨x, hx⟩ := hy
    refine ⟨-x, ?_⟩
    simp only [Pi.neg_apply, Int.cast_neg] at hx ⊢
    rw [hx]
    ring

/-- The coordinate `z` is injective. -/
theorem b3A_φ_injective : Function.Injective b3A_φ := by
  intro w w' h
  rw [b3A_quot_eq w, b3A_quot_eq w', h]

/-- The `dz`-period of `s ⊗ λ_a + t ⊗ λ_b` is `s + t i`. -/
theorem b3A_X_dz (s t : ℝ) :
    b3_cplxPeriod _ _ ((s : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ b3A_loopA +
      (t : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ b3A_loopB) b3A_dz = (s : ℂ) + (t : ℂ) * Complex.I := by
  have ha : b3_pathPeriod _ _ b3_ellipticA b3A_dz = 1 := by
    rw [b3A_ellipticA_eq, b3A_line_pathPeriod, b3A_formFunctional_dz, b3A_φ_e0]
  have hb : b3_pathPeriod _ _ b3_ellipticB b3A_dz = Complex.I := by
    rw [b3A_ellipticB_eq, b3A_line_pathPeriod, b3A_formFunctional_dz, b3A_φ_e1]
  simp only [map_add, b3_cplxPeriod, LinearMap.liftBaseChange_tmul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  change (s : ℂ) * b3_pathPeriod _ _ b3_ellipticA b3A_dz +
    (t : ℂ) * b3_pathPeriod _ _ b3_ellipticB b3A_dz = _
  rw [ha, hb, mul_one]

/-- **The Abel–Jacobi map of the elliptic curve based at `0` is bijective.** -/
theorem b3A_elliptic_abelJacobi_bijective
    (aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic)
    (h : b3_IsAbelJacobi b3_EllipticModel b3_Elliptic 0 aj) :
    Function.Bijective aj := by
  have hap := b3A_elliptic_abelJacobi_apply b3A_loopA b3A_loopB rfl rfl aj h
  constructor
  · intro p q hpq
    obtain ⟨s, t, rfl⟩ := b3A_ellipticPoint_surjective p
    obtain ⟨s', t', rfl⟩ := b3A_ellipticPoint_surjective q
    have h1 := (hap s t).symm.trans (hpq.trans (hap s' t'))
    obtain ⟨ℓ, hℓ⟩ := b3A_jacobian_eq (E := b3_EllipticModel) (C := b3_Elliptic)
      (w := (s : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ b3A_loopA +
        (t : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ b3A_loopB)
      (w' := (s' : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ b3A_loopA +
        (t' : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ b3A_loopB) h1
    have h3 := congrFun hℓ b3A_dz
    have h4 : ((s' : ℂ) + (t' : ℂ) * Complex.I) - ((s : ℂ) + (t : ℂ) * Complex.I) =
        (ℓ : b3_HolForm _ _ → ℂ) b3A_dz :=
      (congrArg₂ (· - ·) (b3A_X_dz s' t').symm (b3A_X_dz s t).symm).trans h3
    obtain ⟨x, hx⟩ := b3A_lattice_dz ℓ
    rw [hx] at h4
    have hre := congrArg Complex.re h4
    have him := congrArg Complex.im h4
    simp at hre him
    rw [b3A_ellipticPoint_eq, b3A_ellipticPoint_eq]
    refine (QuotientAddGroup.eq).2 ⟨x, b3A_φ_injective ?_⟩
    rw [b3A_φ_latticeMap, map_add, map_neg, map_add, map_add, map_smul, map_smul, map_smul,
      map_smul, b3A_φ_e0, b3A_φ_e1]
    apply Complex.ext <;> simp <;> linarith
  · intro j
    obtain ⟨v, hv⟩ := b3A_jacobian_surj j
    refine ⟨b3_ellipticPoint (b3_cplxPeriod _ _ v b3A_dz).re (b3_cplxPeriod _ _ v b3A_dz).im,
      (hap _ _).trans ((b3A_jacobian_mk_eq ?_).trans hv.symm)⟩
    refine b3A_linearDual_ext (b3A_cplxPeriod_mem_linearDual _)
      (b3A_cplxPeriod_mem_linearDual _) ((b3A_X_dz _ _).trans ?_)
    exact Complex.re_add_im _

end Elliptic2

end HodgeLean.Foundations.Program

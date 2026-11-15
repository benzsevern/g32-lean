import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRational

noncomputable section

namespace HodgeLean.Foundations.Program

theorem b6m_linearEquiv_map_torsion {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (e : M ≃ₗ[ℤ] N) :
    (Submodule.torsion ℤ M).map e.toLinearMap = Submodule.torsion ℤ N := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff x).mp hx
    apply (Submodule.mem_torsion_iff (e x)).mpr
    exact ⟨n, (e.map_smul n.1 x).symm.trans ((congrArg e hn).trans e.map_zero)⟩
  · intro hy
    obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff y).mp hy
    refine ⟨e.symm y, (Submodule.mem_torsion_iff (e.symm y)).mpr ⟨n, ?_⟩,
      e.apply_symm_apply y⟩
    exact (e.symm.map_smul n.1 y).symm.trans
      ((congrArg e.symm hn).trans e.symm.map_zero)

theorem b6m_linearEquiv_descend_surjective
    {M N A B : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup A] [AddCommGroup B]
    [Module ℤ M] [Module ℤ N] [Module ℤ A] [Module ℤ B]
    (e : M ≃ₗ[ℤ] N) (P : M →ₗ[ℤ] A) (S : N →ₗ[ℤ] B)
    (hP : Function.Surjective P) (hS : Function.Surjective S)
    (hk : (LinearMap.ker P).map e.toLinearMap = LinearMap.ker S) :
    ∃ T : A ≃ₗ[ℤ] B, ∀ x, T (P x) = S (e x) := by
  let p := P.quotKerEquivOfSurjective hP
  let s := S.quotKerEquivOfSurjective hS
  let q := Submodule.Quotient.equiv (LinearMap.ker P) (LinearMap.ker S) e hk
  refine ⟨p.symm.trans (q.trans s), fun x ↦ ?_⟩
  change s (q (p.symm (P x))) = S (e x)
  have hp : p.symm (P x) = Submodule.Quotient.mk x := by
    apply p.injective
    simp [p, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rw [hp]
  rfl

open scoped Manifold ContDiff

theorem b6m_period_transport_exists (C D : Type)
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    (e : C ≃ₜ D)
    (P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C)
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ)
    (S : b6m_H1 D →ₗ[ℤ] b3_periodLattice ℂ D)
    (hS : ∀ γ : b3_SmoothLoop ℂ D, S (b6m_loopClass D γ) = b3_latticePeriod ℂ D γ) :
    ∃ T : b3_periodLattice ℂ C ≃ₗ[ℤ] b3_periodLattice ℂ D,
      ∀ x, T (P x) = S (b6m_H1Equiv e x) := by
  apply b6m_linearEquiv_descend_surjective (b6m_H1Equiv e) P S
    (b6m_period_map_surjective C P hP) (b6m_period_map_surjective D S hS)
  rw [b6m_period_lattice_kernel C P hP, b6m_period_lattice_kernel D S hS]
  exact b6m_linearEquiv_map_torsion (b6m_H1Equiv e)

theorem b6m_period_transport_unique (C D : Type)
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (e : C ≃ₜ D)
    (P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C)
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ)
    (S : b6m_H1 D →ₗ[ℤ] b3_periodLattice ℂ D)
    (T U : b3_periodLattice ℂ C ≃ₗ[ℤ] b3_periodLattice ℂ D)
    (hT : ∀ x, T (P x) = S (b6m_H1Equiv e x))
    (hU : ∀ x, U (P x) = S (b6m_H1Equiv e x)) : T = U := by
  apply LinearEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := b6m_period_map_surjective C P hP y
  exact (hT x).trans (hU x).symm

theorem b6m_period_transport_loop (C D : Type)
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (e : C ≃ₜ D)
    (P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C)
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ)
    (S : b6m_H1 D →ₗ[ℤ] b3_periodLattice ℂ D)
    (hS : ∀ γ : b3_SmoothLoop ℂ D, S (b6m_loopClass D γ) = b3_latticePeriod ℂ D γ)
    (T : b3_periodLattice ℂ C ≃ₗ[ℤ] b3_periodLattice ℂ D)
    (hT : ∀ x, T (P x) = S (b6m_H1Equiv e x))
    (γ : b3_SmoothLoop ℂ C) (δ : b3_SmoothLoop ℂ D)
    (h : ∀ t : ℝ, e (γ.1 t) = δ.1 t) :
    T (b3_latticePeriod ℂ C γ) = b3_latticePeriod ℂ D δ := by
  rw [← hP γ, hT, b6m_H1Equiv_loopClass e γ δ h, hS]

end HodgeLean.Foundations.Program

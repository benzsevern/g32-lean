import HodgeLean.Foundations.AnalyticAlbanese.Defs

/-! # Period coordinates for maps to a torus

HC no distance; AV milestone no distance.
-/

set_option maxHeartbeats 200000
noncomputable section
open Manifold Filter Topology
open scoped TensorProduct ContDiff
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.AnalyticAlbanese
attribute [local instance] b2_torus_isManifold

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  {Μ : Type} [AddCommGroup Μ] [Module.Finite ℤ Μ]
  (G : Submodule ℂ (ℂ ⊗[ℤ] Μ)) [DiscreteTopology (b2_latticeMap Μ G).range]
  (f : C → b2_torus Μ G) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V Μ G) ω f)

/-- Pull back an invariant coordinate form of the target torus.
HC no distance; AV milestone no distance. -/
def pulledCoordinate (i : Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Μ) ⧸ G))) : b3_HolForm E C :=
  b3A_pullHol f hf ⟨b3A_invForm G (ContinuousLinearMap.proj i),
    b3A_invForm_mem G (ContinuousLinearMap.proj i)⟩

/-- The map on the covering spaces obtained by evaluation on pulled-back forms.
HC no distance; AV milestone no distance. -/
def coordinateLift : ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) →ₗ[ℂ]
    ((ℂ ⊗[ℤ] Μ) ⧸ G) :=
  (b2_coord _).symm.toLinearMap ∘ₗ
    (b3_periodF E C).liftQ
      (LinearMap.pi fun i ↦ (LinearMap.proj (R := ℂ) (φ := fun _ : b3_HolForm E C ↦ ℂ)
        (pulledCoordinate G f hf i)) ∘ₗ b3_cplxPeriod E C)
      (by
        intro v hv
        ext i
        change b3_cplxPeriod E C v (pulledCoordinate G f hf i) = 0
        have hv' : b3_cplxPeriod E C v = 0 := hv
        rw [hv']
        rfl)

/-- The lift evaluates a represented path as the integral of the target velocity.
HC no distance; AV milestone no distance. -/
theorem coordinateLift_path (γ : ℝ → C)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (v : ℂ ⊗[ℤ] b3_periodLattice E C)
    (hv : b3_cplxPeriod E C v = b3_pathPeriod E C γ) :
    coordinateLift G f hf (Submodule.Quotient.mk v) = (b2_coord _).symm
      (∫ t in (0 : ℝ)..1, b3A_vel (E := b5_V Μ G) (C := b2_torus Μ G) (f ∘ γ) t) := by
  apply (b2_coord _).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [coordinateLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  ext i
  change b3_cplxPeriod E C v (pulledCoordinate G f hf i) = _
  rw [hv]
  change b3_pathIntegral E C γ
    (b3_pullback E (b5_V Μ G) f (b3A_invForm G (ContinuousLinearMap.proj i))) = _
  rw [← b3A_pathIntegral_comp f hf γ hγ]
  have hc := b3A_torus_velocity_continuous G (f ∘ γ) (b3A_contMDiff_comp_real f hf γ hγ)
  exact ((ContinuousLinearMap.proj i : b5_V Μ G →L[ℂ] ℂ).intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1))

/-- Path development identifies the quotient of the lift with the endpoint increment.
HC no distance; AV milestone no distance. -/
theorem coordinateLift_increment (γ : ℝ → C)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (v : ℂ ⊗[ℤ] b3_periodLattice E C)
    (hv : b3_cplxPeriod E C v = b3_pathPeriod E C γ) :
    (QuotientAddGroup.mk (coordinateLift G f hf (Submodule.Quotient.mk v)) : b2_torus Μ G) =
      f (γ 1) - f (γ 0) := by
  rw [coordinateLift_path G f hf γ hγ v hv]
  have h := b3A_torus_develop G (f ∘ γ) (b3A_contMDiff_comp_real f hf γ hγ) 1
  change f (γ 1) = f (γ 0) + _ at h
  rw [h, add_sub_cancel_left]

/-- The coordinate lift carries the integral period subgroup into the target subgroup.
HC no distance; AV milestone no distance. -/
theorem coordinateLift_lattice [FiniteDimensional ℂ E] (l : b3_periodLattice E C) :
    coordinateLift G f hf (b2_latticeMap _ (b3_periodF E C) l) ∈
      (b2_latticeMap Μ G).range := by
  let q : b3_periodLattice E C →+ b2_torus Μ G :=
    (QuotientAddGroup.mk' (b2_latticeMap Μ G).range).comp
      ((coordinateLift G f hf).toAddMonoidHom.comp
        (b2_latticeMap _ (b3_periodF E C)))
  have hloop (γ : b3_SmoothLoop E C) : q (b3_latticePeriod E C γ) = 0 := by
    have hv : b3_cplxPeriod E C ((1 : ℂ) ⊗ₜ[ℤ] b3_latticePeriod E C γ) =
        b3_pathPeriod E C γ.1 := by
      simp only [b3_cplxPeriod, LinearMap.liftBaseChange_tmul, one_smul]
      rfl
    have he := coordinateLift_increment G f hf γ.1 γ.2.2 _ hv
    have hp : γ.1 1 = γ.1 0 := by simpa using γ.2.1 0
    rw [hp, sub_self] at he
    exact he
  have hm : l ∈ AddSubgroup.closure (Set.range (b3_latticePeriod E C)) := by
    rw [b3Rest_closure_latticePeriod]
    exact AddSubgroup.mem_top l
  apply (QuotientAddGroup.eq_zero_iff _).1
  change q l = 0
  induction hm using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨γ, rfl⟩ := hx; exact hloop γ
  | zero => exact map_zero q
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]

end HodgeLean.Foundations.AnalyticAlbanese

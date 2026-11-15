import HodgeLean.Foundations.RepFoundations

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

variable {G : Type} [Group G] [Fintype G]

theorem g32c_fixed_eq_zero (σ : FDRep ℂ G) [Simple σ]
    (hnt : ∃ g, σ.ρ g ≠ 1) (v : σ) (hv : ∀ g, σ.ρ g v = v) : v = 0 := by
  classical
  let P : Representation.IntertwiningMap σ.ρ σ.ρ :=
    ⟨∑ h : G, σ.ρ h, fun g => by
      change (∑ h : G, σ.ρ h) * σ.ρ g = σ.ρ g * (∑ h : G, σ.ρ h)
      simp only [Finset.sum_mul, Finset.mul_sum, ← map_mul]
      exact (Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)).trans
        (Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)).symm⟩
  obtain ⟨c, hc⟩ := rfd_intertwining_eq_smul σ P
  have hP (w : σ) : P w = c • w := by
    have := congrArg (fun f : Representation.IntertwiningMap σ.ρ σ.ρ => f w) hc
    exact this
  have hPv : P v = (Fintype.card G : ℂ) • v := by
    change (∑ h : G, σ.ρ h) v = _
    simp only [LinearMap.sum_apply, hv, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  by_contra hv0
  have hcG : c = Fintype.card G := by
    have he : (c - (Fintype.card G : ℂ)) • v = 0 := by
      rw [sub_smul, ← hP, hPv, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right hv0)
  obtain ⟨g, hg⟩ := hnt
  apply hg
  ext w
  have hi : σ.ρ g (P w) = P w := by
    change σ.ρ g ((∑ h : G, σ.ρ h) w) = (∑ h : G, σ.ρ h) w
    simp only [LinearMap.sum_apply, map_sum, ← Module.End.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)
  rw [hP, hcG, map_smul] at hi
  exact (smul_right_injective σ (by simp : (Fintype.card G : ℂ) ≠ 0)) hi

theorem g32c_rank_bound {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    {I : Type} [Fintype I] (a : I → G)
    (hfixed : ∀ v : V, (∀ i, ρ (a i) v = v) → v = 0) :
    Module.finrank ℂ V ≤ ∑ i, Module.finrank ℂ (LinearMap.range (ρ (a i) - 1)) := by
  let F : V →ₗ[ℂ] (∀ i, LinearMap.range (ρ (a i) - 1)) :=
    LinearMap.pi fun i => (ρ (a i) - 1).rangeRestrict
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    apply hfixed v
    intro i
    have he := congrArg (fun z => (z i : V)) hv
    change (ρ (a i) - 1) v = 0 at he
    exact sub_eq_zero.mp he
  simpa only [Module.finrank_pi_fintype] using F.finrank_le_finrank_of_injective hinj

def g32c_rankActionEquiv {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : G) : V ≃ₗ[ℂ] V where
  toLinearMap := ρ h
  invFun := ρ h⁻¹
  left_inv v := by
    change (ρ h⁻¹ * ρ h) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    change (ρ h * ρ h⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

theorem g32c_rank_conjugate {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g h : G) :
    Module.finrank ℂ (LinearMap.range (ρ (h * g * h⁻¹) - 1)) =
      Module.finrank ℂ (LinearMap.range (ρ g - 1)) := by
  have he : (ρ (h * g * h⁻¹) - 1).comp (ρ h) = (ρ h).comp (ρ g - 1) := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub]
    simp only [← Module.End.mul_eq_comp, ← map_mul, one_mul, mul_one]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hr : LinearMap.range (ρ (h * g * h⁻¹) - 1) =
      (LinearMap.range (ρ g - 1)).map (g32c_rankActionEquiv ρ h).toLinearMap := by
    change LinearMap.range (ρ (h * g * h⁻¹) - 1) =
      (LinearMap.range (ρ g - 1)).map (ρ h)
    rw [← LinearMap.range_comp, ← he]
    exact (LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (g32c_rankActionEquiv ρ h).surjective)).symm
  rw [hr]
  exact (g32c_rankActionEquiv ρ h).finrank_map_eq _

theorem g32c_rank_inverse {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    Module.finrank ℂ (LinearMap.range (ρ g⁻¹ - 1)) =
      Module.finrank ℂ (LinearMap.range (ρ g - 1)) := by
  have he : (ρ g⁻¹ - 1).comp (ρ g) = -(ρ g - 1) := by
    rw [LinearMap.sub_comp]
    simp only [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_mul]
    abel
  have hr : LinearMap.range (ρ g⁻¹ - 1) = LinearMap.range (-(ρ g - 1)) := by
    rw [← he]
    exact (LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (g32c_rankActionEquiv ρ g).surjective)).symm
  rw [hr, LinearMap.range_neg]

def g32c_regular : Representation ℂ G (G → ℂ) where
  toFun g :=
    { toFun := fun f x => f (x * g)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext; simp only [mul_one]; rfl
  map_mul' := by intros; ext f x; exact congrArg f (mul_assoc _ _ _).symm

theorem g32c_regular_eigen_pos (H : Subgroup G) (χ : H →* ℂˣ) :
    0 < Module.finrank ℂ (rfd_eigen g32c_regular H χ) := by
  classical
  let f : G → ℂ := fun g => if hg : g ∈ H then (χ ⟨g, hg⟩ : ℂ) else 0
  have hf : f ∈ rfd_eigen g32c_regular H χ := by
    intro h
    funext g
    change f (g * h.1) = (χ h : ℂ) * f g
    by_cases hg : g ∈ H
    · have hgh : g * h.1 ∈ H := H.mul_mem hg h.2
      have he : (⟨g * h.1, hgh⟩ : H) = ⟨g, hg⟩ * h := rfl
      simp only [f, dite_eq_left hg, dite_eq_left hgh, he, map_mul, Units.val_mul]
      exact mul_comm _ _
    · have hgh : g * h.1 ∉ H := by
        intro hh
        exact hg ((H.mul_mem_cancel_right h.2).mp hh)
      simp only [f, dite_eq_right hg, dite_eq_right hgh, mul_zero]
  have hf0 : f ≠ 0 := by
    intro he
    have he1 := congrFun he 1
    have hh : (⟨1, H.one_mem⟩ : H) = 1 := rfl
    have he10 : (1 : ℂ) = 0 := by
      simpa only [f, dite_eq_left H.one_mem, hh, map_one, Units.val_one, Pi.zero_apply] using he1
    exact one_ne_zero he10
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨f, hf⟩, fun h => hf0 (congrArg Subtype.val h)⟩

end HodgeLean.Foundations.Program

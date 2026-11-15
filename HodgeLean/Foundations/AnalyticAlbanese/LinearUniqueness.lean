import HodgeLean.Foundations.AnalyticAlbanese.Defs
import HodgeLean.Foundations.Program.CurveJacobianRest2IntegCurve

/-! # Linear lifts detected by path increments

HC no distance; AV milestone no distance.
-/
set_option maxHeartbeats 400000
noncomputable section
open Manifold Filter Topology
open scoped TensorProduct ContDiff
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.AnalyticAlbanese

/-- A linear map whose represented path increments have zero quotient vanishes.
HC no distance; AV milestone no distance. -/
theorem linear_eq_zero_of_path_classes
    (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1)
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (Μ : Type) [AddCommGroup Μ] [Module.Finite ℤ Μ]
    (G : Submodule ℂ (ℂ ⊗[ℤ] Μ)) [DiscreteTopology (b2_latticeMap Μ G).range]
    (D : ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) →ₗ[ℂ] ((ℂ ⊗[ℤ] Μ) ⧸ G))
    (hD : ∀ (γ : ℝ → C), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ →
      ∀ v : ℂ ⊗[ℤ] b3_periodLattice E C,
        b3_cplxPeriod E C v = b3_pathPeriod E C γ →
        (QuotientAddGroup.mk (D (Submodule.Quotient.mk v)) : b2_torus Μ G) = 0) : D = 0 := by
  letI := b3_holForm_finiteDimensional (E := E) (C := C) hE
  let b := Module.finBasis ℂ (b3_HolForm E C)
  obtain ⟨B, hB⟩ := (b3Rest_evalQ (E := E) (C := C) b).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (b3Rest_evalQ_injective b))
  have hrep (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (t : ℝ) :
      ∃ v : ℂ ⊗[ℤ] b3_periodLattice E C,
        b3_cplxPeriod E C v = b3_pathPeriod E C (fun s ↦ γ (t * s)) ∧
        B (b3Rest2_Γ b γ t) = Submodule.Quotient.mk v := by
    have hγt := b3A_contMDiff_reparam hγ (σ := fun s ↦ t * s)
      (contDiff_const.mul contDiff_id)
    obtain ⟨v, hv⟩ := b3A_exists_cplxPeriod_eq hE _ hγt
    refine ⟨v, hv, ?_⟩
    have he : b3Rest_evalQ b (Submodule.Quotient.mk v) = b3Rest2_Γ b γ t := by
      ext i
      rw [b3Rest_evalQ_mk, hv]
      change b3_pathPeriod E C (fun s ↦ γ (t * s)) (b i) = _
      rw [b3Rest2_pathPeriod_scale hγ]
      rfl
    rw [← he]
    exact LinearMap.congr_fun hB _
  have hloop (γ : b3_SmoothLoop E C) :
      D (b2_latticeMap _ (b3_periodF E C) (b3_latticePeriod E C γ)) = 0 := by
    let w : ℝ → (ℂ ⊗[ℤ] Μ) ⧸ G := fun t ↦ D (B (b3Rest2_Γ b γ.1 t))
    have hw : Continuous w := (IsModuleTopology.continuous_of_linearMap (D.comp B)).comp
      (b3Rest2_continuous_Γ b γ.2.2)
    have hm : ∀ t, w t ∈ (b2_latticeMap Μ G).range := by
      intro t
      obtain ⟨v, hv, he⟩ := hrep γ.1 γ.2.2 t
      change D (B (b3Rest2_Γ b γ.1 t)) ∈ _
      rw [he]
      apply (QuotientAddGroup.eq_zero_iff _).1
      exact hD _ (b3A_contMDiff_reparam γ.2.2
        (σ := fun s ↦ t * s) (contDiff_const.mul contDiff_id)) v hv
    have hconst : ∀ t, w t = w 0 := by
      let z : ℝ → (b2_latticeMap Μ G).range := fun t ↦ ⟨w t, hm t⟩
      have hz : Continuous z := hw.subtype_mk hm
      intro t
      exact congrArg Subtype.val (((IsLocallyConstant.iff_continuous z).2 hz).apply_eq_of_preconnectedSpace t 0)
    have hw0 : w 0 = 0 := by
      simp only [w, b3Rest2_Γ_zero, map_zero]
    have he : b3Rest_evalQ b
        (b2_latticeMap _ (b3_periodF E C) (b3_latticePeriod E C γ)) = b3Rest2_Γ b γ.1 1 := by
      ext i
      change b3_cplxPeriod E C ((1 : ℂ) ⊗ₜ[ℤ] b3_latticePeriod E C γ) (b i) = _
      simp only [b3_cplxPeriod, LinearMap.liftBaseChange_tmul, one_smul]
      rfl
    have hb : B (b3Rest2_Γ b γ.1 1) =
        b2_latticeMap _ (b3_periodF E C) (b3_latticePeriod E C γ) := by
      rw [← he]
      exact LinearMap.congr_fun hB _
    rw [← hb]
    exact (hconst 1).trans hw0
  have hlattice : ∀ l : b3_periodLattice E C,
      D (b2_latticeMap _ (b3_periodF E C) l) = 0 := by
    intro l
    have hm : l ∈ AddSubgroup.closure (Set.range (b3_latticePeriod E C)) := by
      rw [b3Rest_closure_latticePeriod]
      exact AddSubgroup.mem_top l
    induction hm using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨γ, rfl⟩ := hx; exact hloop γ
      | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | neg x _ hx => rw [map_neg, map_neg, hx, neg_zero]
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change D ((b3_periodF E C).mkQ v) = 0
  induction v using TensorProduct.inductionOn with
  | tmul c l =>
    have he : (b3_periodF E C).mkQ (c ⊗ₜ[ℤ] l) =
        c • b2_latticeMap _ (b3_periodF E C) l := by
      rw [show c ⊗ₜ[ℤ] l = c • ((1 : ℂ) ⊗ₜ[ℤ] l) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      rw [map_smul]
      rfl
    rw [he, map_smul, hlattice, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

end HodgeLean.Foundations.AnalyticAlbanese

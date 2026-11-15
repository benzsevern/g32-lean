import HodgeLean.Foundations.Program.HurwitzPrymCovGalois
import HodgeLean.Foundations.Program.HurwitzPrymCovHodge

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: pulling back forms along a Galois cover

The pullback `f^*` sends holomorphic forms on `Y` to `G`-invariant holomorphic forms on `C` (since
`f ∘ g = f`), and it is injective: over a value with an unramified preimage `df` is onto, so a
form with `f^* η = 0` vanishes there, and the finitely many branch values are limits of such
values. Hence `dim Ω¹(Y) ≤ dim Ω¹(C)^G`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Vanish

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]

/-- **A holomorphic form vanishing over a punctured neighborhood vanishes at the point.** -/
theorem b4cov_form_eq_zero_of_eventually (hE' : Module.finrank ℂ E' = 1)
    (η : TangentBundle 𝓘(ℂ, E') Y → ℂ) (hη : η ∈ b3_HolForm E' Y) (y₀ : Y)
    (h : ∀ᶠ y in 𝓝[≠] y₀, ∀ v : E', η ⟨y, v⟩ = 0) (v : E') : η ⟨y₀, v⟩ = 0 := by
  have hne : (𝓝[≠] y₀).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
    intro N hN
    obtain ⟨U, hUN, -, -, -, z, hzU, hzx⟩ := b4cov_goodPoint hE' y₀ N hN
    exact ⟨z, hUN hzU, hzx⟩
  set e := trivializationAt E' (TangentSpace 𝓘(ℂ, E')) y₀
  have hy₀ : y₀ ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source E' y₀
  let w : E' := (e ⟨y₀, v⟩).2
  let s : Y → TangentBundle 𝓘(ℂ, E') Y := fun y ↦ ⟨y, e.symm y w⟩
  have hs : ContMDiffAt 𝓘(ℂ, E') 𝓘(ℂ, E').tangent ω s y₀ := by
    rw [Bundle.contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    have hbase : e.baseSet ∈ 𝓝 y₀ := e.open_baseSet.mem_nhds hy₀
    refine (contMDiffAt_const (c := w)).congr_of_eventuallyEq ?_
    filter_upwards [hbase] with y hy
    change (e ⟨y, e.symm y w⟩).2 = w
    rw [e.apply_mk_symm hy w]
  have hcont : ContinuousAt (η ∘ s) y₀ := ((hη.1 (s y₀)).comp y₀ hs).continuousAt
  have h1 : Tendsto (η ∘ s) (𝓝[≠] y₀) (𝓝 ((η ∘ s) y₀)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (η ∘ s) (𝓝[≠] y₀) (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [h] with y hy
      exact (hy _).symm)
  have h3 := tendsto_nhds_unique h1 h2
  have hsv : e.symm y₀ w = v := e.symm_apply_apply_mk hy₀ v
  change η ⟨y₀, e.symm y₀ w⟩ = 0 at h3
  rwa [hsv] at h3

end Vanish

section Pullback

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]

/-- Pullbacks compose contravariantly (maps into another surface). -/
theorem b4cov_pullback_comp' (f₁ : C → C) (f₂ : C → Y) (h₁ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω f₁)
    (h₂ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f₂) (θ : TangentBundle 𝓘(ℂ, E') Y → ℂ) :
    b3_pullback E E f₁ (b3_pullback E E' f₂ θ) = b3_pullback E E' (f₂ ∘ f₁) θ := by
  funext p
  change θ ⟨f₂ (f₁ p.1), mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f₂ (f₁ p.1)
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) f₁ p.1 p.2)⟩ =
      θ ⟨(f₂ ∘ f₁) p.1, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') (f₂ ∘ f₁) p.1 p.2⟩
  rw [mfderiv_comp_apply (g := f₂) (f := f₁) p.1 ((h₂ _).mdifferentiableAt (by simp))
    ((h₁ _).mdifferentiableAt (by simp))]
  rfl

variable {G : Type} [Group G] [MulAction G C]

/-- **Pulled-back forms are invariant.** -/
theorem b4cov_pullback_mem_invariantForms
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f)
    (η : TangentBundle 𝓘(ℂ, E') Y → ℂ) (hη : η ∈ b3_HolForm E' Y) :
    b3_pullback E E' f η ∈ b4_invariantForms E C G := by
  refine ⟨b3_pullback_mem_holForm f hf η hη, Submodule.mem_iInf _ |>.2 fun g ↦ ?_⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  change b3_pullback E E (fun x : C ↦ g⁻¹ • x) (b3_pullback E E' f η) = _
  rw [b4cov_pullback_comp' _ f (hG g⁻¹) hf]
  have : (f ∘ fun x : C ↦ g⁻¹ • x) = f := funext fun x ↦ hgal.1 g⁻¹ x
  rw [this]

/-- **The pullback of forms along a non-constant map is injective.** -/
theorem b4cov_pullback_injective [T2Space C] [CompactSpace C] [ConnectedSpace C] [T2Space Y]
    [ConnectedSpace Y] (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x')
    (η : TangentBundle 𝓘(ℂ, E') Y → ℂ) (hη : η ∈ b3_HolForm E' Y)
    (h0 : b3_pullback E E' f η = 0) : η = 0 := by
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  have hBfin : (b4_branchSet E E' f).Finite := (b4cov_critical_finite hE f hf hnc).image f |>.subset
    (by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x, ?_, rfl⟩
      by_contra hne
      have := (b4cov_ramIndex_eq_one_iff f hf x).2 hne
      change 2 ≤ b4_ramIndex E E' f x at hx
      omega)
  have hreg : ∀ y, y ∉ b4_branchSet E E' f → ∀ v : E', η ⟨y, v⟩ = 0 := by
    intro y hy v
    obtain ⟨x, rfl⟩ := b4cov_surjective hE' f hf hnc y
    have hram : b4_ramIndex E E' f x = 1 := by
      have h1 := b4cov_ramIndex_pos f hf hnc x
      have h2 : ¬ 2 ≤ b4_ramIndex E E' f x := fun h ↦ hy ⟨x, h, rfl⟩
      omega
    have hd := (b4cov_ramIndex_eq_one_iff f hf x).1 hram
    obtain ⟨u, hu⟩ := (b4cov_bijective_of_ne_zero hE hE'
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x) hd).2 v
    have := congrFun h0 ⟨x, u⟩
    change η ⟨f x, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x u⟩ = 0 at this
    rwa [show mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x u = v from hu] at this
  funext p
  obtain ⟨y, v⟩ := p
  refine b4cov_form_eq_zero_of_eventually hE' η hη y ?_ v
  have hB' : ((b4_branchSet E E' f) \ {y})ᶜ ∈ 𝓝 y :=
    (hBfin.diff).isClosed.isOpen_compl.mem_nhds (fun h ↦ h.2 rfl)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hB', self_mem_nhdsWithin] with y' hy' hy'y
  exact hreg y' fun hB ↦ hy' ⟨hB, hy'y⟩

/-- **`dim Ω¹(Y) ≤ dim Ω¹(C)^G`** for a Galois cover. -/
theorem b4cov_finrank_holForm_le_invariant [Finite G] [Nonempty C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [T2Space Y] [ConnectedSpace Y] (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f) :
    Module.finrank ℂ (b3_HolForm E' Y) ≤ Module.finrank ℂ (b4_invariantForms E C G) := by
  obtain ⟨x₀⟩ := ‹Nonempty C›
  have hnc := b4cov_nonconst_of_galois hE f hgal x₀
  have := b3_holForm_finiteDimensional (C := C) hE
  have : FiniteDimensional ℂ (b4_invariantForms E C G) :=
    Submodule.finiteDimensional_of_le inf_le_left
  let P : b3_HolForm E' Y →ₗ[ℂ] b4_invariantForms E C G :=
    ((b3_pullback E E' f).domRestrict (b3_HolForm E' Y)).codRestrict _ fun η ↦
      b4cov_pullback_mem_invariantForms hG f hf hgal η η.2
  refine LinearMap.finrank_le_finrank_of_injective (f := P) fun η η' h ↦ ?_
  have h' : b3_pullback E E' f ((η : TangentBundle 𝓘(ℂ, E') Y → ℂ) - η') = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val h
  have := b4cov_pullback_injective hE hE' f hf hnc _ (Submodule.sub_mem _ η.2 η'.2) h'
  exact Subtype.ext (sub_eq_zero.1 this)

end Pullback

end HodgeLean.Foundations.Program

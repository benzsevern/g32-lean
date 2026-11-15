import HodgeLean.Foundations.Program.CurveJacobianAPaths

/-! # Track B3, lane A: functoriality and the Abel–Jacobi map

The pushforward `λ ↦ λ ∘ f^*` of period lattices along a holomorphic map, its compatibility with the
filtrations, uniqueness of Abel–Jacobi maps on a connected surface, and their naturality.
-/

noncomputable section

open Manifold Filter Topology
open scoped ContDiff TensorProduct

namespace HodgeLean.Foundations.Program

section Functor

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {C' : Type} [TopologicalSpace C'] [ChartedSpace E' C'] [IsManifold 𝓘(ℂ, E') ω C']

/-- The pullback of holomorphic forms along a holomorphic map. -/
def b3A_pullHol (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) :
    b3_HolForm E' C' →ₗ[ℂ] b3_HolForm E C :=
  (b3_pullback E E' f).restrict fun θ hθ ↦ b3A_pullback_mem_holForm f hf θ hθ

/-- Precomposition with the pullback, on functions of holomorphic forms. -/
def b3A_precomp (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) :
    (b3_HolForm E C → ℂ) →+ (b3_HolForm E' C' → ℂ) where
  toFun u θ := u (b3A_pullHol f hf θ)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Precomposition sends the period of a loop to the period of its image. -/
theorem b3A_precomp_period (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (γ : b3_SmoothLoop E C) (γ' : b3_SmoothLoop E' C') (h : γ'.1 = f ∘ γ.1) :
    b3A_precomp f hf (b3_period E C γ) = b3_period E' C' γ' := by
  funext θ
  change b3_pathIntegral E C γ.1 (b3_pullback E E' f θ) = b3_pathIntegral E' C' γ'.1 θ
  rw [h, b3A_pathIntegral_comp f hf γ.1 γ.2.2]

/-- Precomposition sends the periods of a `C¹` path to the periods of its image. -/
theorem b3A_precomp_pathPeriod (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    b3A_precomp f hf (b3_pathPeriod E C γ) = b3_pathPeriod E' C' (f ∘ γ) := by
  funext θ
  change b3_pathIntegral E C γ (b3_pullback E E' f θ) = b3_pathIntegral E' C' (f ∘ γ) θ
  rw [b3A_pathIntegral_comp f hf γ hγ]

/-- Precomposition maps the period lattice into the period lattice. -/
theorem b3A_precomp_mem (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (u : b3_periodLattice E C) : b3A_precomp f hf u ∈ b3_periodLattice E' C' := by
  have : b3_periodLattice E C ≤ (b3_periodLattice E' C').comap (b3A_precomp f hf) := by
    rw [b3_periodLattice, AddSubgroup.closure_le]
    rintro _ ⟨γ, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap,
      b3A_precomp_period f hf γ (b3A_mapLoop f hf γ) rfl]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩
  exact this u.2

/-- **The pushforward of period lattices**, `λ ↦ λ ∘ f^*`. -/
def b3A_push (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) :
    b3_periodLattice E C →+ b3_periodLattice E' C' :=
  ((b3A_precomp f hf).comp (b3_periodLattice E C).subtype).codRestrict _
    (b3A_precomp_mem f hf)

/-- `λ ↦ λ ∘ f^*` is a pushforward. -/
theorem b3A_push_isPushforward (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) :
    b3_IsPushforward E E' f (b3A_push f hf) := fun γ γ' h ↦
  Subtype.ext (b3A_precomp_period f hf γ γ' h)

/-- The periods of the complexified pushforward of `v` are those of `v` on pulled-back forms. -/
theorem b3A_cplxPeriod_cplxMap (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (g : b3_periodLattice E C →+ b3_periodLattice E' C')
    (hg : ∀ u : b3_periodLattice E C, (g u : b3_HolForm E' C' → ℂ) = b3A_precomp f hf u)
    (v : ℂ ⊗[ℤ] b3_periodLattice E C) :
    b3_cplxPeriod E' C' (b2_cplxMap g v) = b3A_precomp f hf (b3_cplxPeriod E C v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c u =>
    simp only [b2_cplxMap, LinearMap.baseChange_tmul, b3_cplxPeriod,
      LinearMap.liftBaseChange_tmul]
    change c • (g u : b3_HolForm E' C' → ℂ) = b3A_precomp f hf (c • (u : b3_HolForm E C → ℂ))
    rw [hg]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The periods of the complexified pushforward `λ ↦ λ ∘ f^*`. -/
theorem b3A_cplxPeriod_push (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (v : ℂ ⊗[ℤ] b3_periodLattice E C) :
    b3_cplxPeriod E' C' (b2_cplxMap (b3A_push f hf) v) =
      b3A_precomp f hf (b3_cplxPeriod E C v) :=
  b3A_cplxPeriod_cplxMap f hf _ (fun _ ↦ rfl) v

/-- A pushforward exists and respects the filtrations. -/
theorem b3A_exists_pushforward (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) :
    ∃ g : b3_periodLattice E C →+ b3_periodLattice E' C', b3_IsPushforward E E' f g ∧
      b3_periodF E C ≤ (b3_periodF E' C').comap (b2_cplxMap g) := by
  refine ⟨b3A_push f hf, b3A_push_isPushforward f hf, fun v hv ↦ ?_⟩
  simp only [Submodule.mem_comap, b3_periodF, LinearMap.mem_ker] at hv ⊢
  rw [b3A_cplxPeriod_cplxMap f hf _ (fun _ ↦ rfl), hv, map_zero]

omit [IsManifold 𝓘(ℂ, E') ω C'] in
/-- **Abel–Jacobi maps are unique** on a connected surface. -/
theorem b3A_abelJacobi_unique [ConnectedSpace C] (p₀ : C) (aj aj' : C → b3_Jacobian E C)
    (h : b3_IsAbelJacobi E C p₀ aj) (h' : b3_IsAbelJacobi E C p₀ aj') : aj = aj' := by
  funext p
  obtain ⟨γ, hγ⟩ := b3A_joined (E := E) p₀ p
  obtain ⟨v, hv, hv'⟩ := h.2 γ hγ.1
  obtain ⟨w, hw, hw'⟩ := h'.2 γ hγ.1
  simp only [hγ.apply_zero, hγ.apply_one, h.1, sub_zero] at hv'
  simp only [hγ.apply_zero, hγ.apply_one, h'.1, sub_zero] at hw'
  refine hv'.trans (Eq.trans (congrArg (fun z ↦ (QuotientAddGroup.mk z : b3_Jacobian E C))
    ((Submodule.Quotient.eq _).2 (LinearMap.sub_mem_ker_iff.2 (hv.trans hw.symm)))) hw'.symm)

/-- Every pushforward is `λ ↦ λ ∘ f^*`. -/
theorem b3A_pushforward_apply (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (g : b3_periodLattice E C →+ b3_periodLattice E' C') (hg : b3_IsPushforward E E' f g)
    (u : b3_periodLattice E C) : (g u : b3_HolForm E' C' → ℂ) = b3A_precomp f hf u := by
  obtain rfl := b3A_pushforward_unique f hf _ _ hg (b3A_push_isPushforward f hf)
  rfl

/-- **Naturality of the Abel–Jacobi map**: `AJ_{C'} (f p) = J(f)_* (AJ_C p)`. -/
theorem b3A_abelJacobi_natural [ConnectedSpace C]
    (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (g : b3_periodLattice E C →+ b3_periodLattice E' C') (hg : b3_IsPushforward E E' f g)
    (hgF : b3_periodF E C ≤ (b3_periodF E' C').comap (b2_cplxMap g))
    (p₀ : C) (aj : C → b3_Jacobian E C) (haj : b3_IsAbelJacobi E C p₀ aj)
    (aj' : C' → b3_Jacobian E' C') (haj' : b3_IsAbelJacobi E' C' (f p₀) aj') (p : C) :
    aj' (f p) = b2_torusHom (b3_periodF E C) (b3_periodF E' C') g hgF (aj p) := by
  obtain ⟨γ, hγ⟩ := b3A_joined (E := E) p₀ p
  obtain ⟨v, hv, hv'⟩ := haj.2 γ hγ.1
  have hc := b3A_contMDiff_comp_real f hf γ hγ.1
  have h4 := haj'.2 (f ∘ γ) hc
  obtain ⟨w, hww⟩ := h4
  have hw := hww.1
  have hw' := hww.2
  simp only [hγ.apply_zero, hγ.apply_one, haj.1, sub_zero] at hv'
  simp only [Function.comp_apply, hγ.apply_zero, hγ.apply_one, haj'.1, sub_zero] at hw'
  have key : b3_cplxPeriod E' C' w = b3_cplxPeriod E' C' (b2_cplxMap g v) := by
    rw [b3A_cplxPeriod_cplxMap f hf g (b3A_pushforward_apply f hf g hg), hw, hv,
      b3A_precomp_pathPeriod f hf γ hγ.1]
  calc aj' (f p) = QuotientAddGroup.mk (Submodule.Quotient.mk w) := hw'
    _ = QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap g v)) :=
      congrArg (fun z ↦ (QuotientAddGroup.mk z : b3_Jacobian E' C'))
        ((Submodule.Quotient.eq _).2 (LinearMap.sub_mem_ker_iff.2 key))
    _ = b2_torusHom (b3_periodF E C) (b3_periodF E' C') g hgF
        (QuotientAddGroup.mk (Submodule.Quotient.mk v)) := rfl
    _ = b2_torusHom (b3_periodF E C) (b3_periodF E' C') g hgF (aj p) :=
      congrArg _ hv'.symm

end Functor

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.CurveJacobianABasic

/-! # Track B3, lane A: plumbing

Linearity of periods, freeness of the period lattice, antisymmetry of intersection numbers, the
pullback of holomorphic forms, change of variables along holomorphic maps, uniqueness of
pushforwards, and connectedness of the elliptic curve.
-/

noncomputable section

open Manifold Filter Topology
open scoped ContDiff TensorProduct

namespace HodgeLean.Foundations.Program

section Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]


/-- Integrands of holomorphic forms along `C¹` paths are continuous. -/
theorem b3A_continuous_integrand (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (θ : b3_HolForm E C) :
    Continuous (fun t ↦ (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) ⟨γ t, b3_velocity E C γ t⟩) :=
  θ.2.1.continuous.comp (b3A_continuous_velocity γ hγ)

/-- The periods of a `C¹` path are `ℂ`-linear on holomorphic forms. -/
theorem b3A_pathPeriod_linear (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    b3_pathPeriod E C γ ∈ b3_linearDual E C := by
  intro a θ η
  simp only [b3_pathPeriod, b3_pathIntegral, Submodule.coe_add, Submodule.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [intervalIntegral.integral_add ((b3A_continuous_integrand γ hγ θ).intervalIntegrable _ _
      |>.const_mul a) ((b3A_continuous_integrand γ hγ η).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

/-- A finitely generated period lattice is free: it is torsion-free, lying in a `ℂ`-vector space. -/
theorem b3A_periodLattice_free [Module.Finite ℤ (b3_periodLattice E C)] :
    Module.Free ℤ (b3_periodLattice E C) :=
  inferInstance

end Periods

section Inter
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C]

/-- The orientation form is antisymmetric. -/
theorem b3A_orient_swap (v w : E) : b3_orient E w v = -b3_orient E v w := by
  simp only [b3_orient, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- `finsum` over a set commutes with negation, with no finiteness hypothesis. -/
theorem b3A_finsum_mem_neg {α : Type*} (s : Set α) (f : α → ℤ) :
    ∑ᶠ p ∈ s, -f p = -∑ᶠ p ∈ s, f p := by
  rw [finsum_mem_def, finsum_mem_def, ← finsum_neg_distrib]
  congr 1
  funext p
  by_cases h : p ∈ s <;> simp [h]

/-- Intersection numbers are antisymmetric. -/
theorem b3A_intersection_antisymm (γ δ : b3_SmoothLoop E C) :
    b3_intersection E δ γ = -b3_intersection E γ δ := by
  unfold b3_intersection
  rw [← b3A_finsum_mem_neg]
  refine finsum_mem_eq_of_bijOn Prod.swap ?_ ?_
  · refine ⟨fun p hp ↦ ⟨hp.2.1, hp.1, hp.2.2.symm⟩, fun p _ q _ h ↦ Prod.swap_injective h,
      fun p hp ↦ ⟨p.swap, ⟨hp.2.1, hp.1, hp.2.2.symm⟩, rfl⟩⟩
  · intro p _
    rw [b3A_orient_swap (E := E) (b3_velocity E C γ.1 p.2) (b3_velocity E C δ.1 p.1)]
    rw [Left.sign_neg, SignType.coe_neg]
    rfl
end Inter

section Maps
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {C' : Type} [TopologicalSpace C'] [ChartedSpace E' C'] [IsManifold 𝓘(ℂ, E') ω C']

/-- The pullback of a holomorphic form along a holomorphic map is holomorphic. -/
theorem b3A_pullback_mem_holForm (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (θ : TangentBundle 𝓘(ℂ, E') C' → ℂ) (hθ : θ ∈ b3_HolForm E' C') :
    b3_pullback E E' f θ ∈ b3_HolForm E C := by
  refine ⟨?_, fun x a v w ↦ ?_⟩
  · exact hθ.1.comp (hf.contMDiff_tangentMap (by simp))
  · change θ ⟨f x, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x (a • v + w)⟩ =
      a * θ ⟨f x, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x v⟩ + θ ⟨f x, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x w⟩
    rw [map_add, map_smul]
    exact hθ.2 _ _ _ _

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω C'] in
/-- The chain rule for velocities: `(f ∘ γ)' = df (γ')`. -/
theorem b3A_velocity_comp (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (t : ℝ) :
    b3_velocity E' C' (f ∘ γ) t = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f (γ t) (b3_velocity E C γ t) := by
  have hfd := b3A_mdifferentiableAt_real ((hf (γ t)).mdifferentiableAt (by simp))
  exact (mfderiv_comp_apply t hfd.1 ((hγ t).mdifferentiableAt one_ne_zero) 1).trans (hfd.2 _)

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω C'] in
/-- Change of variables for path integrals along a holomorphic map. -/
theorem b3A_pathIntegral_comp (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (θ : TangentBundle 𝓘(ℂ, E') C' → ℂ) :
    b3_pathIntegral E' C' (f ∘ γ) θ = b3_pathIntegral E C γ (b3_pullback E E' f θ) := by
  unfold b3_pathIntegral
  congr 1
  funext t
  rw [b3A_velocity_comp f hf γ hγ t]
  rfl

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω C'] in
/-- A holomorphic map sends `C¹` paths to `C¹` paths. -/
theorem b3A_contMDiff_comp_real (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E') 1 (f ∘ γ) :=
  fun t ↦ (show ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E') 1 f (γ t) from
    (b3A_contMDiffWithinAt_real (hf (γ t))).of_le le_top).comp t (hγ t)

/-- The image of a `C¹` loop under a holomorphic map. -/
def b3A_mapLoop (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (γ : b3_SmoothLoop E C) :
    b3_SmoothLoop E' C' :=
  ⟨f ∘ γ.1, fun t ↦ by simp [γ.2.1 t], b3A_contMDiff_comp_real f hf γ.1 γ.2.2⟩

/-- A pushforward of period lattices is fixed on the generators. -/
theorem b3A_pushforward_unique (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (g g' : b3_periodLattice E C →+ b3_periodLattice E' C')
    (hg : b3_IsPushforward E E' f g) (hg' : b3_IsPushforward E E' f g') :
    g = g' := by
  ext1 ⟨x, hx⟩
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨γ, rfl⟩ := hy
    exact (hg γ (b3A_mapLoop f hf γ) rfl).trans (hg' γ (b3A_mapLoop f hf γ) rfl).symm
  | zero => exact (map_zero g).trans (map_zero g').symm
  | add y z hy hz ihy ihz =>
    have := congrArg₂ (· + ·) ihy ihz
    simp only [← map_add] at this
    exact this
  | neg y hy ih =>
    have := congrArg (- ·) ih
    simp only [← map_neg] at this
    exact this
end Maps

/-- The elliptic curve is connected, as a continuous image of the vector space `ℂ ⊗ ℤ²`. -/
theorem b3A_elliptic_connectedSpace : ConnectedSpace b3_Elliptic := by
  have hj : ∀ x : ℂ ⊗[ℤ] (Fin 2 → ℤ), Joined 0 x := fun x ↦
    ⟨{ toFun := fun t ↦ (((t : ℝ) : ℂ)) • x
       continuous_toFun := (Complex.continuous_ofReal.comp continuous_subtype_val).smul
         continuous_const
       source' := by simp
       target' := by simp }⟩
  have : PathConnectedSpace (ℂ ⊗[ℤ] (Fin 2 → ℤ)) :=
    ⟨⟨0⟩, fun x y ↦ (hj x).symm.trans (hj y)⟩
  have hc : Continuous (fun v : ℂ ⊗[ℤ] (Fin 2 → ℤ) ↦
      (QuotientAddGroup.mk (Submodule.Quotient.mk (p := b2_stdF) v) : b3_Elliptic)) :=
    continuous_quotient_mk'.comp continuous_quotient_mk'
  have hs : Function.Surjective (fun v : ℂ ⊗[ℤ] (Fin 2 → ℤ) ↦
      (QuotientAddGroup.mk (Submodule.Quotient.mk (p := b2_stdF) v) : b3_Elliptic)) :=
    (QuotientAddGroup.mk_surjective).comp (Submodule.Quotient.mk_surjective _)
  rw [connectedSpace_iff_univ]
  have := isConnected_univ.image _ hc.continuousOn
  rwa [Set.image_univ, hs.range_eq] at this

end HodgeLean.Foundations.Program

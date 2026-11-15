import HodgeLean.Foundations.Program.VariationHodgeDefs

/-!
# Abstract polarized variations of Hodge structure: helpers for the period map

Flat transport inside simply connected sets is functorial and independent of the set; the
Hodge numbers of a holomorphic subbundle are locally constant; transport of a polarized
filtration along a flat isometry stays polarized; and the matrix of a projection in a moving
frame is `M D M⁻¹`.
-/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

open HodgeBlocks

section Transport

variable {B : Type*} [TopologicalSpace B]

/-- The class `classIn` is the class of any path that stays in `U`.
Source: Hatcher, *Algebraic Topology*, §1.1, Proposition 1.6. -/
theorem d1per_classIn_eq (U : Set B) (hU : IsSimplyConnected U) (b b' : U)
    (γ : Path (b : B) b') (hγ : ∀ t, γ t ∈ U) :
    d1_LocalSystem.classIn U hU b b' = Path.Homotopic.Quotient.mk γ := by
  have := hU.simplyConnectedSpace
  let γ' : Path b b' :=
    { toFun := fun t ↦ ⟨γ t, hγ t⟩
      continuous_toFun := by fun_prop
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  have hmap : γ'.map continuous_subtype_val = γ := by ext t; rfl
  unfold d1_LocalSystem.classIn
  apply Quotient.sound
  rw [← hmap]
  exact (SimplyConnectedSpace.paths_homotopic (PathConnectedSpace.somePath b b') γ').map
    ⟨Subtype.val, continuous_subtype_val⟩

theorem d1per_classIn_self (U : Set B) (hU : IsSimplyConnected U) (b : U) :
    d1_LocalSystem.classIn U hU b b = Path.Homotopic.Quotient.mk (Path.refl (b : B)) :=
  d1per_classIn_eq U hU b b _ (fun _ ↦ b.2)

theorem d1per_classIn_trans (U : Set B) (hU : IsSimplyConnected U) (b b' b'' : U) :
    (d1_LocalSystem.classIn U hU b b').trans (d1_LocalSystem.classIn U hU b' b'') =
      d1_LocalSystem.classIn U hU b b'' := by
  have := hU.simplyConnectedSpace
  unfold d1_LocalSystem.classIn
  rw [← Path.Homotopic.Quotient.mk_trans, ← Path.map_trans]
  exact (d1per_classIn_eq U hU b b'' _ (fun t ↦ Subtype.mem
    (((PathConnectedSpace.somePath b b').trans (PathConnectedSpace.somePath b' b'')) t))).symm

theorem d1per_classIn_mono (U W : Set B) (hU : IsSimplyConnected U)
    (hW : IsSimplyConnected W) (hWU : W ⊆ U) (b b' : W) :
    d1_LocalSystem.classIn W hW b b' =
      d1_LocalSystem.classIn U hU ⟨b, hWU b.2⟩ ⟨b', hWU b'.2⟩ := by
  have := hW.simplyConnectedSpace
  unfold d1_LocalSystem.classIn
  exact (d1per_classIn_eq U hU ⟨b, hWU b.2⟩ ⟨b', hWU b'.2⟩ _ (fun t ↦ hWU (by simp))).symm

namespace d1_LocalSystem

variable (L : d1_LocalSystem B)

theorem d1per_transport_trans {b b' b'' : B} (γ : Path.Homotopic.Quotient b b')
    (δ : Path.Homotopic.Quotient b' b'') (x : L.fiber b) :
    L.transport (γ.trans δ) x = L.transport δ (L.transport γ x) := by
  show (L.functor.map (_ ≫ _)).hom x = _
  rw [Functor.map_comp]
  rfl

theorem d1per_transport_refl (b : B) (x : L.fiber b) :
    L.transport (Path.Homotopic.Quotient.mk (Path.refl b)) x = x := by
  show (L.functor.map (𝟙 _)).hom x = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem d1per_flatTransport_trans (U : Set B) (hU : IsSimplyConnected U) (b b' b'' : U)
    (x : L.cFiber b) :
    L.flatTransport U hU b' b'' (L.flatTransport U hU b b' x) = L.flatTransport U hU b b'' x := by
  unfold flatTransport
  rw [← d1per_classIn_trans U hU b b' b'']
  induction x using TensorProduct.inductionOn with
  | tmul c w =>
    simp only [LinearEquiv.baseChange_tmul]
    rw [d1per_transport_trans]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem d1per_flatTransport_self (U : Set B) (hU : IsSimplyConnected U) (b : U)
    (x : L.cFiber b) : L.flatTransport U hU b b x = x := by
  unfold flatTransport
  rw [d1per_classIn_self]
  induction x using TensorProduct.inductionOn with
  | tmul c w =>
    simp only [LinearEquiv.baseChange_tmul]
    rw [d1per_transport_refl]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem d1per_flatTransport_mono (U W : Set B) (hU : IsSimplyConnected U)
    (hW : IsSimplyConnected W) (hWU : W ⊆ U) (b b' : W) (x : L.cFiber b) :
    L.flatTransport W hW b b' x = L.flatTransport U hU ⟨b, hWU b.2⟩ ⟨b', hWU b'.2⟩ x := by
  unfold flatTransport
  rw [d1per_classIn_mono U W hU hW hWU]

theorem d1per_flatTransport_symm (U : Set B) (hU : IsSimplyConnected U) (b b' : U)
    (x : L.cFiber b') :
    (L.flatTransport U hU b b').symm x = L.flatTransport U hU b' b x := by
  rw [LinearEquiv.symm_apply_eq, d1per_flatTransport_trans, d1per_flatTransport_self]

end d1_LocalSystem

end Transport

section PolarizedTransport

variable {V V' : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']

theorem d1per_sigmaQ_baseChange (τ : V ≃ₗ[ℚ] V') (x : ℂ ⊗[ℚ] V) :
    sigmaQ V' (LinearEquiv.baseChange ℚ ℂ V V' τ x) =
      LinearEquiv.baseChange ℚ ℂ V V' τ (sigmaQ V x) := by
  show sigmaQR V' _ = LinearEquiv.baseChange ℚ ℂ V V' τ (sigmaQR V x)
  induction x using TensorProduct.inductionOn with
  | tmul c w => simp [LinearEquiv.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem d1per_baseChange_isometry (τ : V ≃ₗ[ℚ] V') (Q : LinearMap.BilinForm ℚ V)
    (Q' : LinearMap.BilinForm ℚ V') (hQ : ∀ x y, Q' (τ x) (τ y) = Q x y) (x y : ℂ ⊗[ℚ] V) :
    Q'.baseChange ℂ (LinearEquiv.baseChange ℚ ℂ V V' τ x) (LinearEquiv.baseChange ℚ ℂ V V' τ y) =
      Q.baseChange ℂ x y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul c w =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul d u => simp [LinearEquiv.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hQ]

theorem d1per_map_sigmaQ_map (τ : V ≃ₗ[ℚ] V') (G : Submodule ℂ (ℂ ⊗[ℚ] V)) :
    (G.map (LinearEquiv.baseChange ℚ ℂ V V' τ).toLinearMap).map (sigmaQ V') =
      (G.map (sigmaQ V)).map (LinearEquiv.baseChange ℚ ℂ V V' τ).toLinearMap := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨sigmaQ V y, ⟨y, hy, rfl⟩, (d1per_sigmaQ_baseChange τ y).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, d1per_sigmaQ_baseChange τ y⟩

theorem d1per_hodgePiece_map (τ : V ≃ₗ[ℚ] V') (n : ℤ) (G : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (pq : ℤ × ℤ) :
    d1_hodgePiece n (fun p ↦ (G p).map (LinearEquiv.baseChange ℚ ℂ V V' τ).toLinearMap) pq =
      (d1_hodgePiece n G pq).map (LinearEquiv.baseChange ℚ ℂ V V' τ).toLinearMap := by
  unfold d1_hodgePiece
  split_ifs
  · rw [d1per_map_sigmaQ_map, Submodule.map_inf _ (LinearEquiv.injective _)]
  · rw [Submodule.map_bot]

theorem d1per_isPolarized_map [Module.Finite ℚ V] [Module.Finite ℚ V'] (τ : V ≃ₗ[ℚ] V')
    {n : ℤ} {Q : LinearMap.BilinForm ℚ V} {Q' : LinearMap.BilinForm ℚ V'}
    {G : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} (hP : d1_IsPolarizedFiltration n Q G)
    (hQ : ∀ x y, Q' (τ x) (τ y) = Q x y) (hnd : Q'.Nondegenerate)
    (hsymm : ∀ x y, Q' x y = ((-1 : ℚ) ^ n) * Q' y x) :
    d1_IsPolarizedFiltration n Q'
      (fun p ↦ (G p).map (LinearEquiv.baseChange ℚ ℂ V V' τ).toLinearMap) := by
  set T := LinearEquiv.baseChange ℚ ℂ V V' τ
  obtain ⟨⟨hanti, ⟨a, ha⟩, ⟨c, hc⟩, hcompl⟩, -, -, hR1, hR2⟩ := hP
  refine ⟨⟨fun p q h ↦ Submodule.map_mono (hanti h), ⟨a, ?_⟩, ⟨c, ?_⟩, fun p ↦ ?_⟩, hnd, hsymm,
    ?_, ?_⟩
  · simp only [ha, Submodule.map_top, LinearEquiv.range]
  · simp only [hc, Submodule.map_bot]
  · rw [d1per_map_sigmaQ_map]
    exact Submodule.isCompl_map T (hcompl p)
  · rintro p _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (d1per_baseChange_isometry τ Q Q' hQ x y).trans (hR1 p x hx y hy)
  · intro p q hpq x hx hx0
    rw [d1per_hodgePiece_map] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    have hx0' : x ≠ 0 := by rintro rfl; exact hx0 (map_zero _)
    show 0 < (Iexp (p - q) * Q'.baseChange ℂ (T x) (sigmaQ V' (T x))).re
    rw [d1per_sigmaQ_baseChange, d1per_baseChange_isometry τ Q Q' hQ]
    exact hR2 p q hpq x hx hx0'

end PolarizedTransport

section HodgeNumbers

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

/-- The rank of a holomorphic subbundle is locally constant.
Source: Huybrechts, *Complex Geometry*, §2.2 (locally free sheaves have locally constant
rank). -/
theorem d1per_finrank_isLocallyConstant (L : d1_LocalSystem B)
    (G : ∀ b, Submodule ℂ (L.cFiber b)) (hG : L.IsHolomorphicSubbundle E G) :
    IsLocallyConstant (fun b ↦ Module.finrank ℂ (G b)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro b₁
  obtain ⟨U, _, h₁, hUo, r, s, _, hs⟩ := hG b₁
  have hr : ∀ b ∈ U, Module.finrank ℂ (G b) = r := fun b hb ↦ by
    rw [← (hs b hb).2, finrank_span_eq_card (hs b hb).1, Fintype.card_fin]
  filter_upwards [hUo.mem_nhds h₁] with b hb
  rw [hr b hb, hr b₁ h₁]

theorem d1per_finrank_eq_of_mem (L : d1_LocalSystem B)
    (G : ∀ b, Submodule ℂ (L.cFiber b)) (hG : L.IsHolomorphicSubbundle E G)
    (U : Set B) (hU : IsSimplyConnected U) {b b' : B} (hb : b ∈ U) (hb' : b' ∈ U) :
    Module.finrank ℂ (G b) = Module.finrank ℂ (G b') :=
  (d1per_finrank_isLocallyConstant E L G hG).apply_eq_of_isPreconnected
    hU.isPathConnected.isConnected.isPreconnected hb hb'

end HodgeNumbers

section Holomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

variable (E) in
include E in
/-- A charted space over a complex normed space is locally path connected, so every open
neighbourhood contains an open neighbourhood joined to its centre.
Source: Mathlib `ChartedSpace.locallyPathConnectedSpace`. -/
theorem d1per_exists_joined_nhds {O : Set B} (hO : IsOpen O) {b : B} (hb : b ∈ O) :
    ∃ W, IsOpen W ∧ b ∈ W ∧ W ⊆ O ∧ ∀ y ∈ W, JoinedIn W y b := by
  have : LocallyPathConnectedSpace B := ChartedSpace.locallyPathConnectedSpace E B
  exact ⟨pathComponentIn O b, hO.pathComponentIn b, mem_pathComponentIn_self hb,
    pathComponentIn_subset, fun y hy ↦ (isPathConnected_pathComponentIn hb).joinedIn y hy b
      (mem_pathComponentIn_self hb)⟩

theorem d1per_flatTransport_eq_of_joinedIn (L : d1_LocalSystem B) (U U' : Set B)
    (hU : IsSimplyConnected U) (hU' : IsSimplyConnected U') {W : Set B} (hWU : W ⊆ U)
    (hWU' : W ⊆ U') {b b' : B} (hb : b ∈ U) (hb' : b' ∈ U) (hbU' : b ∈ U') (hb'U' : b' ∈ U')
    (hj : JoinedIn W b b') (x : L.cFiber b) :
    L.flatTransport U hU ⟨b, hb⟩ ⟨b', hb'⟩ x = L.flatTransport U' hU' ⟨b, hbU'⟩ ⟨b', hb'U'⟩ x := by
  unfold d1_LocalSystem.flatTransport
  rw [d1per_classIn_eq U hU ⟨b, hb⟩ ⟨b', hb'⟩ hj.somePath (fun t ↦ hWU (hj.somePath_mem t)),
    d1per_classIn_eq U' hU' ⟨b, hbU'⟩ ⟨b', hb'U'⟩ hj.somePath (fun t ↦ hWU' (hj.somePath_mem t))]

theorem d1per_flatCoord_of_mem (L : d1_LocalSystem B) (U : Set B) (hU : IsSimplyConnected U)
    (b₀ : U) (s : ∀ b, L.cFiber b) {b : B} (hb : b ∈ U) :
    L.flatCoord U hU b₀ s b = L.flatTransport U hU ⟨b, hb⟩ b₀ (s b) := by
  simp only [d1_LocalSystem.flatCoord, hb, dite_true]

variable (E) {H H' : Type*} [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H]
  [AddCommGroup H'] [Module ℂ H'] [Module.Finite ℂ H']

theorem d1per_isHolomorphicOn_linear (A : H →ₗ[ℂ] H') {f : B → H} {S : Set B}
    (hf : d1_IsHolomorphicOn E f S) : d1_IsHolomorphicOn E (A ∘ f) S := by
  let g : (Fin (Module.finrank ℂ H) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ H') → ℂ) :=
    LinearMap.toContinuousLinearMap
      ((d1_coord H').toLinearMap ∘ₗ A ∘ₗ (d1_coord H).symm.toLinearMap)
  have h : d1_coord H' ∘ (A ∘ f) = g ∘ (d1_coord H ∘ f) := by
    funext b
    simp [g]
  unfold d1_IsHolomorphicOn
  rw [h]
  exact g.contMDiff.comp_contMDiffOn hf

theorem d1per_isHolomorphicOn_congr {f g : B → H} {S : Set B} (hf : d1_IsHolomorphicOn E f S)
    (h : ∀ b ∈ S, g b = f b) : d1_IsHolomorphicOn E g S :=
  ContMDiffOn.congr hf (fun b hb ↦ by simp only [Function.comp_apply, h b hb])

include E in
/-- A charted space over a complex normed space has a basis of simply connected open sets: the
preimages of small balls under a chart.
Source: Hatcher, *Algebraic Topology*, §1.1 (convex sets are contractible); Mathlib
`Convex.contractibleSpace`. -/
theorem d1per_exists_simplyConnected_nhds {O : Set B} (hO : IsOpen O) {b : B} (hb : b ∈ O) :
    ∃ W, IsOpen W ∧ IsSimplyConnected W ∧ b ∈ W ∧ W ⊆ O := by
  let e := chartAt E b
  have hO' : IsOpen (e '' (O ∩ e.source)) :=
    e.isOpen_image_of_subset_source (hO.inter e.open_source) Set.inter_subset_right
  have hbO' : e b ∈ e '' (O ∩ e.source) := ⟨b, ⟨hb, mem_chart_source E b⟩, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO' (e b) hbO'
  have htgt : Metric.ball (e b) ε ⊆ e.target := by
    refine hball.trans ?_
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source hx.2
  refine ⟨e.symm '' Metric.ball (e b) ε,
    e.symm.isOpen_image_of_subset_source Metric.isOpen_ball htgt, ?_,
    ⟨e b, Metric.mem_ball_self hε, e.left_inv (mem_chart_source E b)⟩, ?_⟩
  · have : ContractibleSpace (Metric.ball (e b) ε) :=
      (convex_ball (e b) ε).contractibleSpace ⟨e b, Metric.mem_ball_self hε⟩
    have := (e.symm.homeomorphOfImageSubsetSource htgt rfl).symm.contractibleSpace
    exact SimplyConnectedSpace.ofContractible _
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hball hy
    rw [e.left_inv hx.2]
    exact hx.1

theorem d1per_flatDeriv_congr {f g : B → H} {S : Set B} (hS : IsOpen S) {b : B} (hb : b ∈ S)
    (h : ∀ x ∈ S, f x = g x) (v : E) : d1_flatDeriv E f b v = d1_flatDeriv E g b v := by
  unfold d1_flatDeriv
  have : (d1_coord H ∘ f) =ᶠ[nhds b] (d1_coord H ∘ g) := by
    filter_upwards [hS.mem_nhds hb] with x hx
    simp only [Function.comp_apply, h x hx]
  rw [Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℂ, E))
    (I' := 𝓘(ℂ, Fin (Module.finrank ℂ H) → ℂ)) this]
  rfl

theorem d1per_flatDeriv_linear (A : H →ₗ[ℂ] H') {f : B → H} {S : Set B} (hS : IsOpen S)
    (hf : d1_IsHolomorphicOn E f S) {b : B} (hb : b ∈ S) (v : E) :
    d1_flatDeriv E (A ∘ f) b v = A (d1_flatDeriv E f b v) := by
  let g : (Fin (Module.finrank ℂ H) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ H') → ℂ) :=
    LinearMap.toContinuousLinearMap
      ((d1_coord H').toLinearMap ∘ₗ A ∘ₗ (d1_coord H).symm.toLinearMap)
  have h : d1_coord H' ∘ (A ∘ f) = g ∘ (d1_coord H ∘ f) := by
    funext b
    simp [g]
  have hd : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Fin (Module.finrank ℂ H) → ℂ) (d1_coord H ∘ f) b :=
    (hf.contMDiffAt (hS.mem_nhds hb)).mdifferentiableAt (by simp)
  unfold d1_flatDeriv
  rw [h, mfderiv_comp b g.mdifferentiableAt hd, g.mfderiv_eq]
  change (d1_coord H').symm (d1_coord H' (A ((d1_coord H).symm _))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end Holomorphic

section ChartAlgebra

variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H]

/-- The splitting of `Fin N` as `Fin r ⊕ Fin k` when `r + k = N`. -/
def d1per_sumEquiv {r k N : ℕ} (h : r + k = N) : Fin N ≃ Fin r ⊕ Fin k :=
  (finSumFinEquiv.trans (finCongr h)).symm

theorem d1per_linearIndependent_iff_det {w : Fin (Module.finrank ℂ H) → H} :
    LinearIndependent ℂ w ↔ ((Module.finBasis ℂ H).toMatrix w).det ≠ 0 := by
  rw [← Module.Basis.det_apply, ← isUnit_iff_ne_zero, ← (Module.finBasis ℂ H).is_basis_iff_det]
  exact ⟨fun h ↦ ⟨h, h.span_eq_top_of_card_eq_finrank' (by simp)⟩, And.left⟩

theorem d1per_isCompl_of_linearIndependent {r k : ℕ} {σ : Fin r → H} {c : Fin k → H}
    (h : LinearIndependent ℂ (Sum.elim σ c)) (hrk : r + k = Module.finrank ℂ H) :
    IsCompl (Submodule.span ℂ (Set.range σ)) (Submodule.span ℂ (Set.range c)) := by
  obtain ⟨hσ, hc, hdisj⟩ := linearIndependent_sum.mp h
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at hσ hc hdisj
  refine ⟨hdisj, codisjoint_iff.mpr (Submodule.eq_top_of_finrank_eq ?_)⟩
  have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℂ (Set.range σ))
    (Submodule.span ℂ (Set.range c))
  rw [disjoint_iff.mp hdisj, finrank_bot, finrank_span_eq_card hσ, finrank_span_eq_card hc,
    Fintype.card_fin, Fintype.card_fin] at this
  omega

theorem d1per_linearIndependent_of_isCompl {r k : ℕ} {σ : Fin r → H} {c : Fin k → H}
    (hσ : LinearIndependent ℂ σ) (hc : LinearIndependent ℂ c)
    (h : IsCompl (Submodule.span ℂ (Set.range σ)) (Submodule.span ℂ (Set.range c))) :
    LinearIndependent ℂ (Sum.elim σ c) ∧ r + k = Module.finrank ℂ H := by
  refine ⟨linearIndependent_sum.mpr ⟨hσ, hc, h.disjoint⟩, ?_⟩
  have := Submodule.finrank_add_eq_of_isCompl h
  rwa [finrank_span_eq_card hσ, finrank_span_eq_card hc, Fintype.card_fin,
    Fintype.card_fin] at this

/-- In a basis `w` adapted to `H = G ⊕ K`, the projection onto `G` along `K` has matrix
`M D M⁻¹`, where `M` is the matrix of `w` and `D` the diagonal indicator of the `G`-vectors.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, ch. 1, §5 (Grassmannian charts). -/
theorem d1per_toMatrix_projection {G K : Submodule ℂ H} (h : IsCompl G K)
    {w : Fin (Module.finrank ℂ H) → H} (hw : LinearIndependent ℂ w)
    (S : Fin (Module.finrank ℂ H) → Prop) [DecidablePred S]
    (hG : ∀ j, S j → w j ∈ G) (hK : ∀ j, ¬ S j → w j ∈ K) :
    LinearMap.toMatrix (Module.finBasis ℂ H) (Module.finBasis ℂ H)
        (G.subtype ∘ₗ G.projectionOnto K h) =
      (Module.finBasis ℂ H).toMatrix w * Matrix.diagonal (fun j ↦ if S j then 1 else 0) *
        ((Module.finBasis ℂ H).toMatrix w)⁻¹ := by
  set β := Module.finBasis ℂ H
  set M := β.toMatrix w
  set P := G.subtype ∘ₗ G.projectionOnto K h
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr (d1per_linearIndependent_iff_det.mp hw)
  have hAM : LinearMap.toMatrix β β P * M =
      M * Matrix.diagonal (fun j ↦ if S j then 1 else 0) := by
    ext a j
    rw [Matrix.mul_diagonal]
    have hPw : P (w j) = if S j then w j else 0 := by
      by_cases hj : S j
      · simp [P, hj, Submodule.projectionOnto_apply_of_mem_left h (hG j hj)]
      · simp [P, hj, Submodule.projectionOnto_apply_of_mem_right h (hK j hj)]
    have : (LinearMap.toMatrix β β P * M) a j = β.repr (P (w j)) a := by
      rw [← LinearMap.toMatrix_mulVec_repr (v₁ := β) (v₂ := β) P (w j)]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, M, Module.Basis.toMatrix_apply]
    rw [this, hPw]
    split_ifs <;> simp [M, Module.Basis.toMatrix_apply]
  calc LinearMap.toMatrix β β P = LinearMap.toMatrix β β P * (M * M⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hAM]

theorem d1per_finBasis_span (K : Submodule ℂ H) :
    LinearIndependent ℂ (fun l ↦ (Module.finBasis ℂ K l : H)) ∧
      Submodule.span ℂ (Set.range fun l ↦ (Module.finBasis ℂ K l : H)) = K := by
  refine ⟨(Module.finBasis ℂ K).linearIndependent.map' K.subtype (Submodule.ker_subtype K), ?_⟩
  calc Submodule.span ℂ (Set.range fun l ↦ (Module.finBasis ℂ K l : H))
      = (Submodule.span ℂ (Set.range (Module.finBasis ℂ K))).map K.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]; rfl
    _ = K := by rw [(Module.finBasis ℂ K).span_eq, Submodule.map_top, Submodule.range_subtype]

end ChartAlgebra

section ChartSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B] {S : Set B}
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem d1per_contMDiffOn_det {M : B → Matrix n n ℂ}
    (hM : ∀ i j, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun b ↦ M b i j) S) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun b ↦ (M b).det) S := by
  have h : (fun b ↦ (M b).det) = fun b ↦
      ∑ τ : Equiv.Perm n, ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ i, M b (τ i) i := by
    funext b
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl (fun τ _ ↦ ?_)
    rw [Units.smul_def, zsmul_eq_mul]
  rw [h]
  refine contMDiffOn_finsetSum (fun τ _ ↦ ?_)
  exact contMDiffOn_const.mul (contMDiffOn_finsetProd (fun i _ ↦ hM _ _))

omit [DecidableEq n] in
theorem d1per_contMDiffOn_mul {M M' : B → Matrix n n ℂ}
    (hM : ∀ i j, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun b ↦ M b i j) S)
    (hM' : ∀ i j, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun b ↦ M' b i j) S) (i j : n) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun b ↦ (M b * M' b) i j) S := by
  simp_rw [Matrix.mul_apply]
  exact contMDiffOn_finsetSum (fun l _ ↦ (hM i l).mul (hM' l j))

theorem d1per_contMDiffOn_inv {M : B → Matrix n n ℂ}
    (hM : ∀ i j, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun b ↦ M b i j) S)
    (hdet : ∀ b ∈ S, (M b).det ≠ 0) (i j : n) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun b ↦ (M b)⁻¹ i j) S := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((d1per_contMDiffOn_det hM).inv₀ hdet).mul (d1per_contMDiffOn_det (fun a l ↦ ?_))
  simp only [Matrix.updateRow_apply]
  by_cases ha : a = j
  · simp only [ha, ite_true]
    exact contMDiffOn_const
  · simp only [ha, ite_false]
    exact hM a l

variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H]

omit [DecidableEq n] in
/-- The matrix of a moving frame `σ(b)` extended by a fixed family `c` has `ω`-smooth entries
where the frame is holomorphic. -/
theorem d1per_frame_entries {r k : ℕ} (hrk : r + k = Module.finrank ℂ H) {σ : Fin r → B → H}
    {W : Set B} (hσ : ∀ l, d1_IsHolomorphicOn E (σ l) W) (c : Fin k → H)
    (a j : Fin (Module.finrank ℂ H)) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun b ↦ (Module.finBasis ℂ H).toMatrix
      (fun j ↦ Sum.elim (fun l ↦ σ l b) c (d1per_sumEquiv hrk j)) a j) W := by
  simp only [Module.Basis.toMatrix_apply]
  generalize d1per_sumEquiv hrk j = t
  rcases t with l | l
  · have hl : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, Fin (Module.finrank ℂ H) → ℂ) ω
        (d1_coord H ∘ σ l) W := hσ l
    refine ((contMDiffOn_pi_space.mp hl) a).congr (fun b _ ↦ ?_)
    simp [d1_coord]
  · simp only [Sum.elim_inr]
    exact contMDiffOn_const

end ChartSmooth

section PeriodMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℂ, E) ω B]

theorem d1per_periodMap_of_mem (V : d1_PolarizedVHS E B) (U : Set B) (hU : IsSimplyConnected U)
    (b₀ : U) {b : B} (hb : b ∈ U) (p : ℤ) :
    d1_periodMap V U hU b₀ b p = (V.F p b).map (V.L.flatTransport U hU ⟨b, hb⟩ b₀).toLinearMap := by
  simp only [d1_periodMap, hb, dite_true]

theorem d1per_periodMap_self (V : d1_PolarizedVHS E B) (U : Set B) (hU : IsSimplyConnected U)
    (b₀ : U) (p : ℤ) : d1_periodMap V U hU b₀ b₀ p = V.F p b₀ := by
  rw [d1per_periodMap_of_mem V U hU b₀ b₀.2]
  ext x
  simp only [Submodule.mem_map, LinearEquiv.coe_coe,
    d1_LocalSystem.d1per_flatTransport_self, exists_eq_right]

end PeriodMap

end HodgeLean.Foundations.Program

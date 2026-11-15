import HodgeLean.Foundations.Program.PrymParabolicSaturatedSchur

/-! # Lemmas for stage H5, first part: the isotypic comparison and the deck action on `L`

The vector evaluation `H₁(X̃; ℤ) → K⁴` of an equivariant cocycle, its equivariance, its value on
the saturated cellular lattice (on the line `K e₀`), the vanishing criterion (a cocycle whose
`0`-th coordinate vanishes on `L` is an equivariant coboundary), the comparison map `Θ` with its
image, and the failure of deck stability of `L`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open HodgeLean.Papers Matrix
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

/-! ## Coordinates of cochains -/

section General

variable {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)

omit [Fintype ι] [DecidableEq ι] in
theorem hg6_delta1_coord (c : hg_Edge G r → ι → K) (i : ι) :
    hg2_delta1 K K g (fun ε => c ε i) = fun τ => hg_delta1 K (ι → K) g c τ i := by
  funext τ
  rcases τ with ⟨k, x⟩ | ⟨k, x⟩ <;> rfl

omit [Fintype ι] [DecidableEq ι] in
theorem hg6_delta0_coord (φ : hg_Vert g → ι → K) (i : ι) :
    hg2_delta0 K K g (fun v => φ v i) = fun ε => hg_delta0 K (ι → K) g φ ε i := by
  funext ε
  rcases ε with ⟨k, x⟩ | ⟨k, x⟩ | ⟨k, x⟩ <;> rfl

theorem hg6_coord_mem (c : hg_eqCocycles σ g) (i : ι) :
    (fun ε => c.1 ε i) ∈ LinearMap.ker (hg2_delta1 K K g) := by
  have hc : hg_delta1 K (ι → K) g c.1 = 0 := (Submodule.mem_inf.mp c.2).2
  rw [LinearMap.mem_ker, hg6_delta1_coord, hc]
  rfl

/-- The vector evaluation `[z] ↦ ⟨c, z⟩ ∈ ι → K` of an equivariant cocycle on cellular `H₁`. -/
def hg6_evalVec (c : hg_eqCocycles σ g) : hg2_H1 ℤ g →ₗ[ℤ] (ι → K) :=
  LinearMap.pi fun i => hg2_cocycleEval K g ⟨fun ε => c.1 ε i, hg6_coord_mem σ g c i⟩

theorem hg6_evalVec_mk (c : hg_eqCocycles σ g) (z : LinearMap.ker (hg2_bd1 ℤ g)) :
    hg6_evalVec σ g c (Submodule.Quotient.mk z) = hg6_pairVec c.1 z.1 := by
  funext i
  simp only [hg6_evalVec, LinearMap.pi_apply, hg2_cocycleEval_apply, hg2_evaluation,
    LinearMap.coe_mk, AddHom.coe_mk, Finsupp.linearCombination_apply, hg6_pairVec,
    Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]

theorem hg6_evalVec_add (c d : hg_eqCocycles σ g) :
    hg6_evalVec σ g (c + d) = hg6_evalVec σ g c + hg6_evalVec σ g d := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  funext i
  simp only [Submodule.mkQ_apply, LinearMap.add_apply, Pi.add_apply, hg6_evalVec_mk,
    hg6_pairVec, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Submodule.coe_add,
    smul_eq_mul, mul_add, Finset.sum_add_distrib]

theorem hg6_evalVec_smul (a : K) (c : hg_eqCocycles σ g) :
    hg6_evalVec σ g (a • c) = a • hg6_evalVec σ g c := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  funext i
  simp only [Submodule.mkQ_apply, LinearMap.smul_apply, Pi.smul_apply, hg6_evalVec_mk,
    hg6_pairVec, Finsupp.sum, Finset.sum_apply, Submodule.coe_smul, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- `⟨c, h_* z⟩ = σ(h) ⟨c, z⟩`. -/
theorem hg6_evalVec_act (c : hg_eqCocycles σ g) (h : G) (x : hg2_H1 ℤ g) :
    hg6_evalVec σ g c (hg2_H1act ℤ g h x) = σ h *ᵥ hg6_evalVec σ g c x := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  have hc : c.1 ∈ hg_eqCochain1 σ := (Submodule.mem_inf.mp c.2).1
  have hact : ∀ ε, c.1 (hg2_actEdge h ε) = σ h *ᵥ c.1 ε := fun ε => by
    rcases ε with ⟨k, y⟩ | ⟨k, y⟩ | ⟨k, y⟩
    · exact hc h (Sum.inl (k, y))
    · exact hc h (Sum.inr (Sum.inl (k, y)))
    · exact hc h (Sum.inr (Sum.inr (k, y)))
  change hg6_evalVec σ g c (Submodule.Quotient.mk ⟨hg2_chainAct1 ℤ h z.1, _⟩) = _
  rw [Submodule.mkQ_apply, hg6_evalVec_mk, hg6_evalVec_mk]
  simp only [hg2_chainAct1, Finsupp.lmapDomain_apply, hg6_pairVec]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
  simp only [hact, Finsupp.sum, Matrix.mulVec_sum, Matrix.mulVec_smul]

/-- A cocycle that is a (not necessarily equivariant) coboundary coordinatewise has zero
evaluation; conversely, zero evaluation makes it an equivariant coboundary. -/
theorem hg6_evalVec_eq_zero_of_mem (c : hg_eqCocycles σ g)
    (hc : c.1 ∈ hg_eqCoboundaries σ g) : hg6_evalVec σ g c = 0 := by
  obtain ⟨φ, -, hφ⟩ := hc
  apply LinearMap.ext
  intro x
  funext i
  have hi : hg2_cocycleEval K g ⟨fun ε => c.1 ε i, hg6_coord_mem σ g c i⟩ = 0 := by
    apply hg2_cocycleEval_coboundary
    refine ⟨fun v => φ v i, ?_⟩
    rw [hg6_delta0_coord]
    funext ε
    rw [hφ]
  change hg2_cocycleEval K g ⟨fun ε => c.1 ε i, hg6_coord_mem σ g c i⟩ x = 0
  rw [hi]
  rfl

theorem hg6_mem_coboundaries_of_evalVec [Fintype G] (hprod : (List.ofFn g).prod = 1)
    (hG : (Fintype.card G : K) ≠ 0) (c : hg_eqCocycles σ g) (h0 : hg6_evalVec σ g c = 0) :
    c.1 ∈ hg_eqCoboundaries σ g := by
  have hcoord : ∀ i, ∃ φ : hg_Vert g → K, hg2_delta0 K K g φ = fun ε => c.1 ε i := by
    intro i
    obtain ⟨e, he⟩ := hg2_uct_aux K g hprod
    have hz : hg2_uctMap K g (Submodule.Quotient.mk ⟨fun ε => c.1 ε i, hg6_coord_mem σ g c i⟩) =
        0 := by
      apply LinearMap.ext
      intro x
      change hg6_evalVec σ g c x i = 0
      rw [h0]
      rfl
    have hz' := hg2_uctMap_injective K g (hz.trans (map_zero _).symm)
    obtain ⟨φ, hφ⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz'
    exact ⟨φ, hφ⟩
  choose φ hφ using hcoord
  have hrange : c.1 ∈ LinearMap.range (hg_delta0 K (ι → K) g) := by
    refine ⟨fun v i => φ i v, ?_⟩
    funext ε i
    have h := congrFun (hg6_delta0_coord g (fun v i => φ i v) i) ε
    rw [← h, hφ i]
  exact hg_eqCoboundary_average σ g hG c.1 (Submodule.mem_inf.mp c.2).1 hrange

end General

/-! ## The comparison on the saturated cellular lattice -/

theorem hg6_card_ne_zero : (Fintype.card b4b_Group : hp_K) ≠ 0 :=
  hg6_natCast_ne_zero _ Fintype.card_ne_zero

theorem hg6_sigma_scalar :
    hg4_sigmaK b63d_scalarElement = pc_zeta • (1 : Matrix (Fin 4) (Fin 4) hp_K) := by
  apply Matrix.map_injective hp_embed.injective
  show (hg4_sigmaK _).map hp_embed = (pc_zeta • (1 : Matrix (Fin 4) (Fin 4) hp_K)).map hp_embed
  rw [hg4_sigmaK_map, b63d_scalarElement_matrix, ← hp_embed_zeta_eq]
  ext i j
  simp [Matrix.one_apply]
  split_ifs <;> simp

/-- The evaluation of an equivariant cocycle on `P w` lies on `K e₀`, with `0`-th coordinate
`D ⟨c, w⟩₀`. -/
theorem hg6_evalVec_projector (c : hg_eqCocycles hg4_sigmaK b4b_root)
    (w : hg2_H1 ℤ b4b_root) :
    hg6_evalVec hg4_sigmaK b4b_root c (hg2_projector w) =
      b4b_projectorDenominator •
        (Pi.single 0 (hg6_evalVec hg4_sigmaK b4b_root c w 0) : Fin 4 → hp_K) := by
  have hP : hg2_projector w = ∑ h, b4b_projectorCoeff h • hg2_H1act ℤ b4b_root h w :=
    hg6_projOf_apply (hg2_H1act ℤ b4b_root) w
  rw [hP, map_sum]
  simp only [map_zsmul, hg6_evalVec_act]
  set v := hg6_evalVec hg4_sigmaK b4b_root c w
  have hs : ∑ h, b4b_projectorCoeff h • (hg4_sigmaK h *ᵥ v) =
      (∑ h, b4b_projectorCoeff h • hg4_sigmaK h) *ᵥ v := by
    rw [Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec]
  rw [hs, hg6_sigma_projector, Matrix.smul_mulVec, Matrix.single_mulVec, one_mul]
  rfl

theorem hg6_projector_mem_lattice (w : hg2_H1 ℤ b4b_root) : hg2_projector w ∈ hg6_cellLattice :=
  (hg6_mem_saturation_iff _ _).mpr ⟨1, one_ne_zero, w, by rw [one_smul]⟩

theorem hg6_zsmul_eq_zero_K {n : ℤ} (hn : n ≠ 0) {a : hp_K} (h : n • a = 0) : a = 0 := by
  rw [zsmul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (Int.cast_ne_zero.mpr hn)

/-- On the saturated cellular lattice the evaluation lies on the line `K e₀`. -/
theorem hg6_evalVec_lattice (c : hg_eqCocycles hg4_sigmaK b4b_root) (x : hg2_H1 ℤ b4b_root)
    (hx : x ∈ hg6_cellLattice) (i : Fin 4) (hi : i ≠ 0) :
    hg6_evalVec hg4_sigmaK b4b_root c x i = 0 := by
  obtain ⟨n, hn, y, hy⟩ := (hg6_mem_saturation_iff _ _).mp hx
  have h := congrFun (hg6_evalVec_projector c y) i
  rw [hy, map_zsmul] at h
  simp only [Pi.smul_apply, Pi.single_apply, hi, ite_false, smul_zero] at h
  exact hg6_zsmul_eq_zero_K hn h

/-- The vanishing criterion: if the `0`-th coordinate of `⟨c, x⟩` vanishes for every `x ∈ L`,
then `c` is an equivariant coboundary. -/
theorem hg6_mem_coboundaries_of_lattice (c : hg_eqCocycles hg4_sigmaK b4b_root)
    (h0 : ∀ x ∈ hg6_cellLattice, hg6_evalVec hg4_sigmaK b4b_root c x 0 = 0) :
    c.1 ∈ hg_eqCoboundaries hg4_sigmaK b4b_root := by
  apply hg6_mem_coboundaries_of_evalVec hg4_sigmaK b4b_root b63d_root_product hg6_card_ne_zero c
  have hv0 : ∀ w, hg6_evalVec hg4_sigmaK b4b_root c w 0 = 0 := fun w => by
    have h := congrFun (hg6_evalVec_projector c w) 0
    rw [h0 _ (hg6_projector_mem_lattice w)] at h
    simp only [Pi.smul_apply, Pi.single_eq_same] at h
    exact hg6_zsmul_eq_zero_K (by norm_num [b4b_projectorDenominator]) h.symm
  apply LinearMap.ext
  intro w
  apply hg6_sigma_irreducible
  intro h
  rw [← hg6_evalVec_act]
  exact hv0 _

/-- The comparison on cocycles: `c ↦ (q ⊗ x ↦ q ⟨c, x⟩₀)`. -/
def hg6_thetaCocycle :
    hg_eqCocycles hg4_sigmaK b4b_root →ₗ[hp_K] ((ℚ ⊗[ℤ] hg6_cellLattice) →ₗ[ℚ] hp_K) where
  toFun c := LinearMap.liftBaseChange ℚ
    ((LinearMap.proj (R := ℤ) (φ := fun _ : Fin 4 => hp_K) 0 ∘ₗ
      hg6_evalVec hg4_sigmaK b4b_root c) ∘ₗ hg6_cellLattice.subtype)
  map_add' c d := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q x
    simp only [LinearMap.liftBaseChange_tmul, LinearMap.add_apply, LinearMap.comp_apply,
      hg6_evalVec_add, LinearMap.proj_apply, Pi.add_apply, smul_add]
  map_smul' a c := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q x
    simp only [LinearMap.liftBaseChange_tmul, LinearMap.smul_apply, LinearMap.comp_apply,
      hg6_evalVec_smul, LinearMap.proj_apply, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [mul_smul_comm]

theorem hg6_thetaCocycle_tmul (c : hg_eqCocycles hg4_sigmaK b4b_root) (q : ℚ)
    (x : hg6_cellLattice) :
    hg6_thetaCocycle c (q ⊗ₜ x) = q • hg6_evalVec hg4_sigmaK b4b_root c x 0 := by
  simp only [hg6_thetaCocycle, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.liftBaseChange_tmul,
    LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply]

/-- The comparison `Θ : H¹_σ → Hom_ℚ(ℚ ⊗ L, K)`. -/
def hg6_theta :
    hg_eqH1 hg4_sigmaK b4b_root →ₗ[hp_K] ((ℚ ⊗[ℤ] hg6_cellLattice) →ₗ[ℚ] hp_K) :=
  Submodule.liftQ _ hg6_thetaCocycle (fun c hc => by
    rw [LinearMap.mem_ker]
    apply TensorProduct.AlgebraTensorModule.ext
    intro q x
    rw [hg6_thetaCocycle_tmul, hg6_evalVec_eq_zero_of_mem _ _ c hc]
    simp)

theorem hg6_theta_mk (c : hg_eqCocycles hg4_sigmaK b4b_root)
    (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
    (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice) :
    hg6_theta (Submodule.Quotient.mk c) ((1 : ℚ) ⊗ₜ[ℤ] ⟨Submodule.Quotient.mk z, hz⟩) =
      hg6_pairVec c.1 z.1 0 := by
  change hg6_thetaCocycle c _ = _
  rw [hg6_thetaCocycle_tmul, one_smul]
  change hg6_evalVec hg4_sigmaK b4b_root c (Submodule.Quotient.mk z) 0 = _
  rw [hg6_evalVec_mk]

theorem hg6_theta_injective : Function.Injective hg6_theta := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ y
  rw [LinearMap.mem_ker] at hy
  rw [Submodule.mem_bot]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply hg6_mem_coboundaries_of_lattice
  intro x hx
  have h := congrArg (fun φ => φ ((1 : ℚ) ⊗ₜ[ℤ] (⟨x, hx⟩ : hg6_cellLattice))) hy
  change hg6_thetaCocycle c _ = 0 at h
  rw [hg6_thetaCocycle_tmul, one_smul] at h
  exact h

/-! ## The image of `Θ` -/

/-- The functionals `φ` with `φ ∘ (1 + 2Z) = √−3 · φ`. -/
def hg6_isoSpace : Submodule hp_K ((ℚ ⊗[ℤ] hg6_cellLattice) →ₗ[ℚ] hp_K) where
  carrier := {φ | ∀ x, φ (hg6_cellJ x) = QuadraticAlgebra.omega * φ x}
  add_mem' {φ ψ} hφ hψ x := by
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ x, hψ x, mul_add]
  zero_mem' x := by simp
  smul_mem' a φ hφ x := by
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ x, smul_eq_mul]
    ring

theorem hg6_one_add_two_zeta : (1 : hp_K) + 2 * pc_zeta = QuadraticAlgebra.omega := by
  rw [pc_zeta]
  ring

theorem hg6_evalVec_cellOperator (c : hg_eqCocycles hg4_sigmaK b4b_root) (x : hg6_cellLattice) :
    hg6_evalVec hg4_sigmaK b4b_root c (hg6_cellOperator x : hg2_H1 ℤ b4b_root) 0 =
      QuadraticAlgebra.omega * hg6_evalVec hg4_sigmaK b4b_root c x 0 := by
  have hop : (hg6_cellOperator x : hg2_H1 ℤ b4b_root) = x.val + 2 • hg6_cellCentre x.val := rfl
  rw [hop, map_add, map_nsmul, hg6_cellCentre, hg6_centreOf_eq, hg6_evalVec_act,
    hg6_sigma_scalar, Matrix.smul_mulVec, Matrix.one_mulVec, ← hg6_one_add_two_zeta]
  simp only [two_nsmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem hg6_theta_le : LinearMap.range hg6_theta ≤ hg6_isoSpace := by
  rintro _ ⟨y, rfl⟩ x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ y
  change hg6_thetaCocycle c (hg6_cellJ x) = QuadraticAlgebra.omega * hg6_thetaCocycle c x
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    rw [hg6_cellJ, LinearMap.baseChange_tmul, hg6_thetaCocycle_tmul, hg6_thetaCocycle_tmul,
      hg6_evalVec_cellOperator, mul_smul_comm]
  | add a b ha hb => simp only [map_add, ha, hb, mul_add]

instance hg6_cellLattice_free : Module.Free ℤ hg6_cellLattice :=
  Module.Free.of_basis (Classical.choice hg6_cellLattice_basis_lemma)

instance hg6_cellLattice_finite : Module.Finite ℤ hg6_cellLattice :=
  Module.Finite.of_basis (Classical.choice hg6_cellLattice_basis_lemma)

theorem hg6_ratLattice_finrank : Module.finrank ℚ (ℚ ⊗[ℤ] hg6_cellLattice) = 12 := by
  rw [Module.finrank_baseChange, hg6_cellLattice_finrank]

/-- The rational part `re : K → ℚ`. -/
def hg6_reₗ : hp_K →ₗ[ℚ] ℚ where
  toFun := QuadraticAlgebra.re
  map_add' _ _ := rfl
  map_smul' _ _ := by simp

/-- `φ ↦ re ∘ φ` on the image space. -/
def hg6_reMap : hg6_isoSpace →ₗ[ℚ] Module.Dual ℚ (ℚ ⊗[ℤ] hg6_cellLattice) where
  toFun φ := hg6_reₗ ∘ₗ φ.1
  map_add' φ ψ := by
    ext x
    simp [hg6_reₗ]
  map_smul' q φ := by
    ext x
    simp [hg6_reₗ]

theorem hg6_reMap_injective : Function.Injective hg6_reMap := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro φ hφ
  rw [LinearMap.mem_ker] at hφ
  rw [Submodule.mem_bot]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  have h1 : (φ.1 x).re = 0 := LinearMap.congr_fun hφ x
  have h2 : (φ.1 (hg6_cellJ x)).re = 0 := LinearMap.congr_fun hφ (hg6_cellJ x)
  rw [φ.2 x] at h2
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega,
    zero_mul, zero_add, mul_one] at h2
  have him : (φ.1 x).im = 0 := by linarith
  exact QuadraticAlgebra.ext h1 him

theorem hg6_eqH1_finrank_lemma : Module.finrank hp_K (hg_eqH1 hg4_sigmaK b4b_root) = 6 := by
  rw [← (LinearEquiv.ofBijective _ (hg4_shapiroH1_bijective hg4_sigmaK b4b_root
    b63d_root_product)).finrank_eq, hg4_sigmaK_tuple, hp_vparK_finrank]

theorem hg6_theta_range : LinearMap.range hg6_theta = hg6_isoSpace := by
  have : Module.Finite ℚ hg6_isoSpace := Module.Finite.of_injective hg6_reMap hg6_reMap_injective
  have : FiniteDimensional hp_K hg6_isoSpace :=
    Module.Finite.of_restrictScalars_finite ℚ hp_K hg6_isoSpace
  have hle : Module.finrank ℚ hg6_isoSpace ≤ 12 := by
    have := LinearMap.finrank_le_finrank_of_injective hg6_reMap_injective
    rwa [Subspace.dual_finrank_eq, hg6_ratLattice_finrank] at this
  have hmul := Module.finrank_mul_finrank ℚ hp_K hg6_isoSpace
  rw [QuadraticAlgebra.finrank_eq_two] at hmul
  have hr : Module.finrank hp_K (LinearMap.range hg6_theta) = 6 := by
    rw [LinearMap.finrank_range_of_inj hg6_theta_injective, hg6_eqH1_finrank_lemma]
  exact Submodule.eq_of_le_of_finrank_le hg6_theta_le (by omega)

theorem hg6_isotypic_comparison_lemma :
    ∃ Θ : hg_eqH1 hg4_sigmaK b4b_root →ₗ[hp_K] ((ℚ ⊗[ℤ] hg6_cellLattice) →ₗ[ℚ] hp_K),
      Function.Injective Θ ∧
      (∀ φ, φ ∈ LinearMap.range Θ ↔
        ∀ x, φ (hg6_cellJ x) = QuadraticAlgebra.omega * φ x) ∧
      ∀ (c : hg_eqCocycles hg4_sigmaK b4b_root) (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
        (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
        Θ (Submodule.Quotient.mk c) ((1 : ℚ) ⊗ₜ[ℤ] ⟨Submodule.Quotient.mk z, hz⟩) =
          hg6_pairVec c.1 z.1 0 :=
  ⟨hg6_theta, hg6_theta_injective, fun φ => by rw [hg6_theta_range]; rfl, hg6_theta_mk⟩

/-! ## The deck action does not preserve `L` -/

theorem hg6_sigma_inv (h : b4b_Group) : hg4_sigmaK h⁻¹ = (hg4_sigmaK h)ᴴ := by
  calc hg4_sigmaK h⁻¹ = (hg4_sigmaK h)ᴴ * hg4_sigmaK h * hg4_sigmaK h⁻¹ := by
        rw [hg6_sigma_unitary, Matrix.one_mul]
    _ = (hg4_sigmaK h)ᴴ := by
        rw [Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]

theorem hg6_lattice_not_deck_stable_lemma :
    ∃ h : b4b_Group, ∃ x ∈ hg6_cellLattice, hg2_H1act ℤ b4b_root h x ∉ hg6_cellLattice := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < Module.finrank hp_K (hg_eqH1 hg4_sigmaK b4b_root) := by
    rw [hg6_eqH1_finrank_lemma]
    norm_num
  obtain ⟨y, hy⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ y
  have hex : ∃ x ∈ hg6_cellLattice, hg6_evalVec hg4_sigmaK b4b_root c x 0 ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hy ((Submodule.Quotient.mk_eq_zero _).mpr (hg6_mem_coboundaries_of_lattice c h'))
  obtain ⟨x, hx, hx0⟩ := hex
  have hcol : ∀ (h : b4b_Group) (i : Fin 4), i ≠ 0 → hg4_sigmaK h i 0 = 0 := by
    intro h i hi
    have h1 := hg6_evalVec_lattice c _ (hcon h x hx) i hi
    rw [hg6_evalVec_act] at h1
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      hg6_evalVec_lattice c x hx 1 (by decide), hg6_evalVec_lattice c x hx 2 (by decide),
      hg6_evalVec_lattice c x hx 3 (by decide)] at h1
    simp only [mul_zero, add_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right hx0
  have hrow : ∀ h : b4b_Group, hg4_sigmaK h 0 1 = 0 := by
    intro h
    have h1 := hcol h⁻¹ 1 (by decide)
    rw [hg6_sigma_inv, Matrix.conjTranspose_apply] at h1
    exact star_eq_zero.mp h1
  have h1 := hg6_sigma_irreducible (Pi.single 1 1) (fun h => by
    simp [Matrix.mulVec_single, hrow h])
  have h2 := congrFun h1 1
  simp at h2

end HodgeLean.Foundations.Program

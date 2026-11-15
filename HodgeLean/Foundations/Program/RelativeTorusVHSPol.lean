import HodgeLean.Foundations.Program.RelativeTorusVHSDefs

/-!
# The cohomology variation of a B2 torus family: the Hodge property and the dual polarization

Helpers for `RelativeTorusVHSProofs.lean`.  The evaluation pairing
`ℂ ⊗ Hom(Λ, ℚ) → Hom(ℂ ⊗ Λ, ℂ)` is an isomorphism compatible with conjugation, so the
annihilators of `F` and `F̄` are complementary and conjugate.  For a nondegenerate form `Q`, the
complexified musical map `w ↦ Q_ℂ(w, ·)` carries `Q_ℂ` to the complexified dual form and `F` onto
the annihilator of `F` when `F` is isotropic.
HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped TensorProduct Matrix

namespace HodgeLean.Foundations.Program

open HodgeBlocks

section Pairing

variable (Λ : Type) [AddCommGroup Λ]

theorem b2bpol_pairing_tmul (c : ℂ) (φ : b2b_dual Λ) (d : ℂ) (x : Λ) :
    b2b_pairing Λ (c ⊗ₜ φ) (d ⊗ₜ x) = c * (d * (φ x : ℂ)) := by
  simp [b2b_pairing, b2b_cplxForm]

theorem b2bpol_pairing_bijective [Module.Free ℤ Λ] [Module.Finite ℤ Λ] :
    Function.Bijective (b2b_pairing Λ) := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let B₁ : Module.Basis _ ℂ (ℂ ⊗[ℚ] b2b_dual Λ) :=
    ((Pi.basisFun ℚ _).map (b.constr ℚ)).baseChange ℂ
  let B₂ := (b.baseChange ℂ).dualBasis
  have h : b2b_pairing Λ = (B₁.equiv B₂ (Equiv.refl _)).toLinearMap := by
    refine B₁.ext fun i ↦ (b.baseChange ℂ).ext fun j ↦ ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply,
      Module.Basis.dualBasis_apply_self]
    simp only [B₁, Module.Basis.baseChange_apply, Module.Basis.map_apply, Pi.basisFun_apply,
      b2bpol_pairing_tmul, Module.Basis.constr_basis]
    by_cases hij : j = i
    · subst hij
      simp
    · simp [hij]
  rw [h]
  exact (B₁.equiv B₂ (Equiv.refl _)).bijective

theorem b2bpol_pairing_sigma (c : ℂ ⊗[ℚ] b2b_dual Λ) (w : ℂ ⊗[ℤ] Λ) :
    b2b_pairing Λ (sigmaQ _ c) w = starRingEnd ℂ (b2b_pairing Λ c (b2_conj Λ w)) := by
  induction c using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add, LinearMap.add_apply, map_add]
  | tmul c φ =>
    induction w using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, map_add]
    | tmul d x =>
      rw [show sigmaQ (b2b_dual Λ) (c ⊗ₜ φ) = starRingEnd ℂ c ⊗ₜ φ from sigmaQ_tmul _ c φ,
        b2a_conj_tmul, b2bpol_pairing_tmul, b2bpol_pairing_tmul]
      simp

theorem b2bpol_sigma_mem_hodgeOne (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (c : ℂ ⊗[ℚ] b2b_dual Λ) :
    sigmaQ _ c ∈ b2b_hodgeOne Λ F ↔ c ∈ b2b_hodgeOne Λ (b2_conjSubmodule Λ F) := by
  simp only [b2b_hodgeOne, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  constructor
  · intro h w hw
    obtain ⟨a, ha, rfl⟩ := b2a_mem_conjSubmodule.1 hw
    have := h a ha
    rw [b2bpol_pairing_sigma] at this
    simpa using this
  · intro h a ha
    rw [b2bpol_pairing_sigma, h _ (b2a_conj_mem_conjSubmodule ha), map_zero]

theorem b2bpol_map_sigma_hodgeOne (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) :
    (b2b_hodgeOne Λ F).map (sigmaQ (b2b_dual Λ)) = b2b_hodgeOne Λ (b2_conjSubmodule Λ F) := by
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact (b2bpol_sigma_mem_hodgeOne Λ F _).1 (by rwa [sigmaQ_involutive])
  · intro hc
    exact ⟨sigmaQ _ c, (b2bpol_sigma_mem_hodgeOne Λ F c).2 hc, sigmaQ_involutive _ c⟩

theorem b2bpol_hodgeOne_isCompl [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    IsCompl (b2b_hodgeOne Λ F) ((b2b_hodgeOne Λ F).map (sigmaQ (b2b_dual Λ))) := by
  rw [b2bpol_map_sigma_hodgeOne]
  exact (Submodule.orderIsoMapComapOfBijective _ (b2bpol_pairing_bijective Λ)).symm.isCompl_iff.1
    (Subspace.isCompl_dualAnnihilator hF)

theorem b2bpol_filtration_of_le_zero (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) {p : ℤ} (hp : p ≤ 0) :
    b2b_filtration Λ F p = ⊤ := by
  simp [b2b_filtration, b2b_weightOne, hp]

theorem b2bpol_filtration_one (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) :
    b2b_filtration Λ F 1 = b2b_hodgeOne Λ F := by
  simp [b2b_filtration, b2b_weightOne]

theorem b2bpol_filtration_of_two_le (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) {p : ℤ} (hp : 2 ≤ p) :
    b2b_filtration Λ F p = ⊥ := by
  simp [b2b_filtration, b2b_weightOne, show ¬ p ≤ 0 by omega, show p ≠ 1 by omega]

theorem b2bpol_filtration_isHodge [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    d1_IsHodgeFiltration 1 (b2b_filtration Λ F) := by
  refine ⟨fun a b hab ↦ ?_, ⟨0, b2bpol_filtration_of_le_zero Λ F le_rfl⟩,
    ⟨2, b2bpol_filtration_of_two_le Λ F le_rfl⟩, fun p ↦ ?_⟩
  · simp only [b2b_filtration, b2b_weightOne]
    split_ifs <;> first | exact le_top | exact bot_le | exact le_rfl | omega
  · by_cases hp0 : p ≤ 0
    · rw [b2bpol_filtration_of_le_zero Λ F hp0, b2bpol_filtration_of_two_le Λ F (by omega),
        Submodule.map_bot]
      exact isCompl_top_bot
    · by_cases hp1 : p = 1
      · subst hp1
        rw [show (1 : ℤ) - 1 + 1 = 1 by norm_num, b2bpol_filtration_one]
        exact b2bpol_hodgeOne_isCompl Λ F hF
      · rw [b2bpol_filtration_of_two_le Λ F (by omega),
          b2bpol_filtration_of_le_zero Λ F (by omega), d1_map_sigmaQ_top]
        exact isCompl_bot_top

end Pairing

/-! ## The dual form -/

section DualForm

variable (Λ : Type) [AddCommGroup Λ]

theorem b2bpol_flat_bijective [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : ∀ u, (∀ v, Q u v = 0) → u = 0) :
    Function.Bijective (b2b_flat Λ Q) := by
  have hinj₀ : Function.Injective (Q.compr₂ (Algebra.linearMap ℤ ℚ)) := by
    intro x y hxy
    apply sub_eq_zero.mp (hQ (x - y) fun z ↦ by
      have := LinearMap.congr_fun hxy z
      change ((Q x z : ℤ) : ℚ) = (Q y z : ℤ) at this
      have hz : Q x z = Q y z := by exact_mod_cast this
      simpa using sub_eq_zero.mpr hz)
  have hinj : Function.Injective (b2b_flat Λ Q) := by
    rw [b2b_flat, LinearMap.liftBaseChange_injective_iff _ (Module.Free.chooseBasis ℤ Λ),
      ← LinearIndependent.iff_fractionRing ℤ ℚ]
    exact (Module.Free.chooseBasis ℤ Λ).linearIndependent.map' _
      (LinearMap.ker_eq_bot.mpr hinj₀)
  have hsurj : Function.Surjective (b2b_flat Λ Q) := by
    rw [← LinearMap.range_eq_top, b2b_flat, LinearMap.range_liftBaseChange]
    change Submodule.span ℚ (LinearMap.range
      (Q.compr₂ (Algebra.linearMap ℤ ℚ)) : Set (b2b_dual Λ)) = ⊤
    apply Submodule.span_range_eq_top_of_injective_of_rank_le
    · exact hinj₀
    · simpa only [Cardinal.lift_id] using
        (Module.rank_linearMap_self (R := ℤ) (S := ℚ) (M := Λ)).le
  exact ⟨hinj, hsurj⟩

theorem b2bpol_dualForm_flat (Q : LinearMap.BilinForm ℤ Λ)
    (h : Function.Bijective (b2b_flat Λ Q)) (a b : ℚ ⊗[ℤ] Λ) :
    b2b_dualForm Λ Q (b2b_flat Λ Q a) (b2b_flat Λ Q b) = Q.baseChange ℚ a b := by
  simp only [b2b_dualForm, h, dite_true]
  change Q.baseChange ℚ
    ((LinearEquiv.ofBijective (b2b_flat Λ Q) h).symm (b2b_flat Λ Q a))
    ((LinearEquiv.ofBijective (b2b_flat Λ Q) h).symm (b2b_flat Λ Q b)) = _
  simp

theorem b2bpol_flat_apply (Q : LinearMap.BilinForm ℤ Λ) (a : ℚ ⊗[ℤ] Λ) (v : Λ) :
    b2b_flat Λ Q a v = Q.baseChange ℚ a ((1 : ℚ) ⊗ₜ v) := by
  induction a using TensorProduct.inductionOn with
  | tmul q u =>
    rw [LinearMap.BilinForm.baseChange_tmul]
    simp [b2b_flat, mul_comm]
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, map_add, LinearMap.add_apply]

theorem b2bpol_baseChange_skew {A : Type} [CommRing A] (Q : LinearMap.BilinForm ℤ Λ)
    (hQ : ∀ x, Q x x = 0) (u v : A ⊗[ℤ] Λ) : Q.baseChange A u v = -Q.baseChange A v u := by
  have hs : ∀ x y, Q x y = -Q y x := fun x y ↦ by
    have := hQ (x + y)
    simp only [map_add, LinearMap.add_apply, hQ, zero_add, add_zero] at this
    exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans this)
  induction u using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, map_add, neg_add]
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, map_add, LinearMap.add_apply, hy, hz, neg_add]
    | tmul b y =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hs,
        neg_smul, mul_comm]

theorem b2bpol_dualForm_skew [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : ∀ x, Q x x = 0)
    (h : Function.Bijective (b2b_flat Λ Q)) (φ ψ : b2b_dual Λ) :
    b2b_dualForm Λ Q φ ψ = -b2b_dualForm Λ Q ψ φ := by
  obtain ⟨a, rfl⟩ := h.2 φ
  obtain ⟨b, rfl⟩ := h.2 ψ
  rw [b2bpol_dualForm_flat Λ Q h, b2bpol_dualForm_flat Λ Q h, b2bpol_baseChange_skew Λ Q hQ]

theorem b2bpol_dualForm_nondegenerate (Q : LinearMap.BilinForm ℤ Λ) (hQ : ∀ x, Q x x = 0)
    (h : Function.Bijective (b2b_flat Λ Q)) : (b2b_dualForm Λ Q).Nondegenerate := by
  have hl : LinearMap.SeparatingLeft (b2b_dualForm Λ Q) := by
    intro φ hφ
    obtain ⟨a, rfl⟩ := h.2 φ
    have ha : b2b_flat Λ Q a = 0 := by
      apply LinearMap.ext
      intro v
      rw [b2bpol_flat_apply, ← b2bpol_dualForm_flat Λ Q h, hφ]
      rfl
    exact ha
  refine ⟨hl, fun ψ hψ ↦ hl ψ fun φ ↦ ?_⟩
  obtain ⟨a, rfl⟩ := h.2 φ
  obtain ⟨b, rfl⟩ := h.2 ψ
  rw [b2bpol_dualForm_flat Λ Q h, b2bpol_baseChange_skew Λ Q hQ, ← b2bpol_dualForm_flat Λ Q h,
    hψ, neg_zero]

/-- Precomposition with an isomorphism of lattices carrying `Q` to `Q'` carries the dual form of
`Q` to the dual form of `Q'`. -/
theorem b2bpol_dualForm_comp {Λ' : Type} [AddCommGroup Λ'] (Q : LinearMap.BilinForm ℤ Λ)
    (Q' : LinearMap.BilinForm ℤ Λ') (e : Λ ≃+ Λ') (he : ∀ x y, Q' (e x) (e y) = Q x y)
    (φ ψ : b2b_dual Λ) :
    b2b_dualForm Λ' Q' (φ ∘ₗ e.symm.toIntLinearEquiv.toLinearMap)
      (ψ ∘ₗ e.symm.toIntLinearEquiv.toLinearMap) = b2b_dualForm Λ Q φ ψ := by
  let eq : ℚ ⊗[ℤ] Λ ≃ₗ[ℚ] ℚ ⊗[ℤ] Λ' := LinearEquiv.baseChange ℤ ℚ _ _ e.toIntLinearEquiv
  let pre : b2b_dual Λ → b2b_dual Λ' := fun φ ↦ φ ∘ₗ e.symm.toIntLinearEquiv.toLinearMap
  have hpre : Function.Bijective pre := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun φ ↦ φ ∘ₗ e.toIntLinearEquiv.toLinearMap, fun φ ↦ ?_, fun φ ↦ ?_⟩ <;>
    · apply LinearMap.ext
      intro x
      simp [pre]
  have hcomm : ∀ a, b2b_flat Λ' Q' (eq a) = pre (b2b_flat Λ Q a) := by
    intro a
    apply LinearMap.ext
    intro v
    induction a using TensorProduct.inductionOn with
    | tmul q u =>
      simp only [eq, pre, LinearEquiv.baseChange_tmul]
      simp [b2b_flat, ← he u (e.symm v)]
    | add x y hx hy =>
      rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add]
      rfl
  have hbase : ∀ a b, Q'.baseChange ℚ (eq a) (eq b) = Q.baseChange ℚ a b := by
    intro a b
    induction a using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
        LinearMap.add_apply]
    | tmul q u =>
      induction b using TensorProduct.inductionOn with
      | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
      | tmul r w =>
        simp only [eq, LinearEquiv.baseChange_tmul]
        rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]
        simp [he]
  have hbij : Function.Bijective (b2b_flat Λ' Q') ↔ Function.Bijective (b2b_flat Λ Q) := by
    rw [← Function.Bijective.of_comp_iff (b2b_flat Λ' Q') eq.bijective,
      ← Function.Bijective.of_comp_iff' hpre (b2b_flat Λ Q)]
    have : (b2b_flat Λ' Q' ∘ eq) = pre ∘ b2b_flat Λ Q := funext hcomm
    rw [this]
  by_cases h : Function.Bijective (b2b_flat Λ Q)
  · have h' := hbij.2 h
    obtain ⟨a, rfl⟩ := h.2 φ
    obtain ⟨b, rfl⟩ := h.2 ψ
    change b2b_dualForm Λ' Q' (pre _) (pre _) = _
    rw [← hcomm, ← hcomm, b2bpol_dualForm_flat Λ' Q' h', b2bpol_dualForm_flat Λ Q h, hbase]
  · have h' : ¬ Function.Bijective (b2b_flat Λ' Q') := fun h' ↦ h (hbij.1 h')
    simp [b2b_dualForm, h, h']

end DualForm

/-! ## The complexified musical map -/

section Musical

variable (Λ : Type) [AddCommGroup Λ]

/-- The complexified musical map `ℂ ⊗[ℤ] Λ → ℂ ⊗[ℚ] Hom(Λ, ℚ)`, `c ⊗ u ↦ c ⊗ Q(u, ·)`. -/
def b2bpol_musical (Q : LinearMap.BilinForm ℤ Λ) : ℂ ⊗[ℤ] Λ →ₗ[ℂ] ℂ ⊗[ℚ] b2b_dual Λ :=
  (b2b_flat Λ Q).baseChange ℂ ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ Λ).symm.toLinearMap

theorem b2bpol_musical_tmul (Q : LinearMap.BilinForm ℤ Λ) (c : ℂ) (u : Λ) :
    b2bpol_musical Λ Q (c ⊗ₜ u) = c ⊗ₜ b2b_flat Λ Q ((1 : ℚ) ⊗ₜ u) := rfl

theorem b2bpol_musical_bijective (Q : LinearMap.BilinForm ℤ Λ)
    (h : Function.Bijective (b2b_flat Λ Q)) : Function.Bijective (b2bpol_musical Λ Q) :=
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ Λ).symm.trans
    (LinearEquiv.baseChange ℚ ℂ _ _ (LinearEquiv.ofBijective _ h))).bijective

theorem b2bpol_pairing_musical (Q : LinearMap.BilinForm ℤ Λ) (w w' : ℂ ⊗[ℤ] Λ) :
    b2b_pairing Λ (b2bpol_musical Λ Q w) w' = Q.baseChange ℂ w w' := by
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply]
  | tmul c u =>
    induction w' using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, map_add, hy, hz]
    | tmul d v =>
      rw [b2bpol_musical_tmul, b2bpol_pairing_tmul, LinearMap.BilinForm.baseChange_tmul]
      simp [b2b_flat]
      ring

theorem b2bpol_dualForm_musical (Q : LinearMap.BilinForm ℤ Λ)
    (h : Function.Bijective (b2b_flat Λ Q)) (w w' : ℂ ⊗[ℤ] Λ) :
    (b2b_dualForm Λ Q).baseChange ℂ (b2bpol_musical Λ Q w) (b2bpol_musical Λ Q w') =
      Q.baseChange ℂ w w' := by
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply]
  | tmul c u =>
    induction w' using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
    | tmul d v =>
      rw [b2bpol_musical_tmul, b2bpol_musical_tmul, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, b2bpol_dualForm_flat Λ Q h,
        LinearMap.BilinForm.baseChange_tmul]
      simp [Rat.smul_def]

theorem b2bpol_sigma_musical (Q : LinearMap.BilinForm ℤ Λ) (w : ℂ ⊗[ℤ] Λ) :
    sigmaQ _ (b2bpol_musical Λ Q w) = b2bpol_musical Λ Q (b2_conj Λ w) := by
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul c u =>
    rw [b2bpol_musical_tmul, b2a_conj_tmul, b2bpol_musical_tmul]
    exact sigmaQ_tmul _ c _

theorem b2bpol_baseChange_conj (Q : LinearMap.BilinForm ℤ Λ) (w w' : ℂ ⊗[ℤ] Λ) :
    Q.baseChange ℂ (b2_conj Λ w) (b2_conj Λ w') = starRingEnd ℂ (Q.baseChange ℂ w w') := by
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply, map_add]
  | tmul c u =>
    induction w' using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, map_add]
    | tmul d v =>
      rw [b2a_conj_tmul, b2a_conj_tmul, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul]
      simp

variable [Module.Free ℤ Λ] [Module.Finite ℤ Λ]

/-- For a Riemann form, the musical map carries `F` onto the annihilator line `F¹`. -/
theorem b2bpol_hodgeOne_eq_map (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (Q : LinearMap.BilinForm ℤ Λ)
    (hF : b2_IsWeightOne Λ F) (hQ : b2_IsRiemannForm Λ F Q)
    (h : Function.Bijective (b2b_flat Λ Q)) :
    b2b_hodgeOne Λ F = F.map (b2bpol_musical Λ Q) := by
  ext c
  constructor
  · intro hc
    obtain ⟨w, rfl⟩ := (b2bpol_musical_bijective Λ Q h).2 c
    have hmem : w ∈ F ⊔ b2_conjSubmodule Λ F := hF.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hmem
    have hy0 : b2bpol_musical Λ Q y = 0 := by
      apply (b2bpol_pairing_bijective Λ).1
      rw [map_zero]
      apply LinearMap.ext
      intro z
      have hz : z ∈ F ⊔ b2_conjSubmodule Λ F := hF.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.1 hz
      simp only [map_add, LinearMap.zero_apply, b2bpol_pairing_musical]
      have h1 : Q.baseChange ℂ y f = 0 := by
        have := (Submodule.mem_dualAnnihilator _).1 hc f hf
        rw [b2bpol_pairing_musical, map_add, LinearMap.add_apply, hQ.isotropic x hx f hf,
          zero_add] at this
        exact this
      have h2 : Q.baseChange ℂ y g = 0 := by
        obtain ⟨y', hy', rfl⟩ := b2a_mem_conjSubmodule.1 hy
        obtain ⟨g', hg', rfl⟩ := b2a_mem_conjSubmodule.1 hg
        rw [b2bpol_baseChange_conj, hQ.isotropic y' hy' g' hg', map_zero]
      rw [h1, h2, add_zero]
    have hy00 : y = 0 := (b2bpol_musical_bijective Λ Q h).1 (by rw [hy0, map_zero])
    rw [hy00, add_zero]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine (Submodule.mem_dualAnnihilator _).2 fun f hf ↦ ?_
    rw [b2bpol_pairing_musical]
    exact hQ.isotropic x hx f hf

theorem b2bpol_dualForm_isPolarized (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (Q : LinearMap.BilinForm ℤ Λ) (hF : b2_IsWeightOne Λ F) (hQ : b2_IsRiemannForm Λ F Q) :
    d1_IsPolarizedFiltration 1 (b2b_dualForm Λ Q) (b2b_filtration Λ F) := by
  have h : Function.Bijective (b2b_flat Λ Q) :=
    b2bpol_flat_bijective Λ Q fun u hu ↦ b2_riemannForm_nondegenerate F Q hF hQ u hu
  have hH := b2bpol_hodgeOne_eq_map Λ F Q hF hQ h
  refine ⟨b2bpol_filtration_isHodge Λ F hF, b2bpol_dualForm_nondegenerate Λ Q hQ.alt h,
    fun x y ↦ ?_, fun p x hx y hy ↦ ?_, fun p q hpq x hx hx0 ↦ ?_⟩
  · rw [b2bpol_dualForm_skew Λ Q hQ.alt h]
    simp
  · by_cases hp0 : p ≤ 0
    · rw [b2bpol_filtration_of_two_le Λ F (by omega)] at hy
      rw [(Submodule.mem_bot ℂ).1 hy, map_zero]
    · by_cases hp1 : p = 1
      · subst hp1
        rw [show (1 : ℤ) - 1 + 1 = 1 by norm_num, b2bpol_filtration_one, hH] at hy
        rw [b2bpol_filtration_one, hH] at hx
        obtain ⟨x, hx', rfl⟩ := hx
        obtain ⟨y, hy', rfl⟩ := hy
        rw [b2bpol_dualForm_musical Λ Q h]
        exact hQ.isotropic x hx' y hy'
      · rw [b2bpol_filtration_of_two_le Λ F (by omega)] at hx
        rw [(Submodule.mem_bot ℂ).1 hx, map_zero, LinearMap.zero_apply]
  · simp only [d1_hodgePiece, hpq, ite_true] at hx
    obtain ⟨hxp, hxq⟩ := Submodule.mem_inf.1 hx
    by_cases hp1 : p = 1
    · subst hp1
      obtain rfl : q = 0 := by omega
      rw [b2bpol_filtration_one, hH] at hxp
      obtain ⟨w, hw, rfl⟩ := hxp
      have hw0 : w ≠ 0 := by rintro rfl; exact hx0 (map_zero _)
      rw [b2bpol_sigma_musical, b2bpol_dualForm_musical Λ Q h,
        show Iexp (1 - 0) = Complex.I by simp [Iexp]]
      exact hQ.positive w hw hw0
    · by_cases hp0 : p = 0
      · subst hp0
        obtain rfl : q = 1 := by omega
        rw [b2bpol_filtration_one, hH] at hxq
        obtain ⟨y, ⟨w, hw, rfl⟩, rfl⟩ := hxq
        have hw0 : w ≠ 0 := by
          rintro rfl
          exact hx0 (by rw [map_zero, map_zero])
        change (0 : ℝ) < (Iexp (0 - 1) * (b2b_dualForm Λ Q).baseChange ℂ
          (sigmaQ _ (b2bpol_musical Λ Q w)) (sigmaQ _ (sigmaQ _ (b2bpol_musical Λ Q w)))).re
        rw [sigmaQ_involutive, b2bpol_sigma_musical, b2bpol_dualForm_musical Λ Q h,
          b2bpol_baseChange_skew Λ Q hQ.alt, show Iexp (0 - 1) = -Complex.I by
            simp [Iexp, zpow_neg, Complex.inv_I], neg_mul_neg]
        exact hQ.positive w hw hw0
      · exfalso
        apply hx0
        by_cases hp2 : 2 ≤ p
        · rw [b2bpol_filtration_of_two_le Λ F hp2] at hxp
          exact (Submodule.mem_bot ℂ).1 hxp
        · rw [b2bpol_filtration_of_two_le Λ F (by omega), Submodule.map_bot] at hxq
          exact (Submodule.mem_bot ℂ).1 hxq

end Musical

/-! ## Marked coordinates -/

section Marked

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

/-- The coordinates `ℚ^n ≃ ℚ ⊗[ℤ] ℤ^n`, `w ↦ ∑ w_k ⊗ e_k`. -/
def b2bpol_coord : (Fin n → ℚ) ≃ₗ[ℚ] ℚ ⊗[ℤ] (Fin n → ℤ) :=
  ((Pi.basisFun ℤ (Fin n)).baseChange ℚ).equivFun.symm

theorem b2bpol_coord_apply (w : Fin n → ℚ) :
    b2bpol_coord w = ∑ k, w k • ((1 : ℚ) ⊗ₜ[ℤ] (Pi.single k 1 : Fin n → ℤ)) := by
  simp [b2bpol_coord, Module.Basis.equivFun_symm_apply]

theorem b2bpol_flat_coord_single (w : Fin n → ℚ) (j : Fin n) :
    b2b_flat (Fin n → ℤ) (Matrix.toLinearMap₂' ℤ A) (b2bpol_coord w) (Pi.single j 1) =
      (w ᵥ* A.map (Int.cast : ℤ → ℚ)) j := by
  rw [b2bpol_coord_apply, map_sum, LinearMap.sum_apply]
  simp [b2b_flat, Matrix.vecMul, dotProduct, Matrix.toLinearMap₂'_apply', Pi.single_apply]

theorem b2bpol_marked_flat_coord (w : Fin n → ℚ) :
    ((Pi.basisFun ℤ (Fin n)).constr ℚ).symm
        (b2b_flat (Fin n → ℤ) (Matrix.toLinearMap₂' ℤ A) (b2bpol_coord w)) =
      w ᵥ* A.map (Int.cast : ℤ → ℚ) := by
  funext j
  rw [Module.Basis.constr_symm_apply]
  simpa using b2bpol_flat_coord_single A w j

theorem b2bpol_baseChange_coord (w w' : Fin n → ℚ) :
    LinearMap.BilinForm.baseChange ℚ (Matrix.toLinearMap₂' ℤ A) (b2bpol_coord w)
        (b2bpol_coord w') =
      (w ᵥ* A.map (Int.cast : ℤ → ℚ)) ⬝ᵥ w' := by
  conv_lhs => rw [b2bpol_coord_apply w']
  simp only [map_sum, map_smul]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← b2bpol_flat_apply, b2bpol_flat_coord_single, smul_eq_mul, mul_comm]

theorem b2bpol_marked_flat_bijective_iff :
    Function.Bijective (b2b_flat (Fin n → ℤ) (Matrix.toLinearMap₂' ℤ A)) ↔
      IsUnit (A.map (Int.cast : ℤ → ℚ)) := by
  let m := ((Pi.basisFun ℤ (Fin n)).constr ℚ (M' := ℚ)).symm
  have hcomp : (⇑m ∘ b2b_flat (Fin n → ℤ) (Matrix.toLinearMap₂' ℤ A)) ∘ ⇑b2bpol_coord =
      fun w ↦ w ᵥ* A.map (Int.cast : ℤ → ℚ) :=
    funext fun w ↦ b2bpol_marked_flat_coord A w
  rw [← Function.Bijective.of_comp_iff' m.bijective,
    ← Function.Bijective.of_comp_iff _ b2bpol_coord.bijective, hcomp]
  constructor
  · intro h
    exact Matrix.vecMul_injective_iff_isUnit.1 h.1
  · intro h
    exact ⟨Matrix.vecMul_injective_iff_isUnit.2 h, Matrix.vecMul_surjective_iff_isUnit.2 h⟩

theorem b2bpol_marked_dualForm (φ ψ : b2b_dual (Fin n → ℤ)) :
    b2b_dualForm (Fin n → ℤ) (Matrix.toLinearMap₂' ℤ A) φ ψ =
      d2_dualForm A (((Pi.basisFun ℤ (Fin n)).constr ℚ).symm φ)
        (((Pi.basisFun ℤ (Fin n)).constr ℚ).symm ψ) := by
  by_cases h : Function.Bijective (b2b_flat (Fin n → ℤ) (Matrix.toLinearMap₂' ℤ A))
  · have hA := (b2bpol_marked_flat_bijective_iff A).1 h
    obtain ⟨w, rfl⟩ := (h.2.comp b2bpol_coord.surjective) φ
    obtain ⟨w', rfl⟩ := (h.2.comp b2bpol_coord.surjective) ψ
    simp only [Function.comp_apply]
    rw [b2bpol_dualForm_flat _ _ h, b2bpol_baseChange_coord, b2bpol_marked_flat_coord,
      b2bpol_marked_flat_coord, d2_dualForm, Matrix.toBilin'_apply', ← Matrix.mulVec_transpose (A.map (Int.cast : ℤ → ℚ)) w',
      Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA), Matrix.transpose_one,
      Matrix.one_mulVec]
  · have hA : ¬ IsUnit (A.map (Int.cast : ℤ → ℚ)) := fun hA ↦
      h ((b2bpol_marked_flat_bijective_iff A).2 hA)
    rw [show b2b_dualForm (Fin n → ℤ) (Matrix.toLinearMap₂' ℤ A) = 0 by simp [b2b_dualForm, h],
      d2_dualForm, Matrix.nonsing_inv_apply_not_isUnit _
        ((Matrix.isUnit_iff_isUnit_det _).not.1 hA)]
    simp

end Marked

end HodgeLean.Foundations.Program

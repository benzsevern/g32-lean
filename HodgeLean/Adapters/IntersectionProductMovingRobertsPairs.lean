import HodgeLean.Adapters.IntersectionProductMovingRobertsFinite

/-! # Pairs of points with the same projection

Roberts' main lemma compares a residual component of `C_L(Z) ∩ X` with `Z` through pairs of
points of `X` with the same image under the projection `π_ℓ`. These pairs are the points of the
doubled coordinate ring `ℂ[x_σ ⊔ x_σ]` (the affine cone over `X ×_{ℙⁿ} X`) containing
`a3r_pairIdeal I ℓ`: both copies lie in `V(I)` and the two projections agree.

* `a3r_exists_common_field`: two primes over the same prime are the kernels of two maps to a
  common field that agree on the base (the fibre `κ(q₁) ⊗_{κ(p)} κ(q₂)` is nonzero);
* `a3r_exists_pair_prime`: hence two points of `V(I)` with the same projection are the two
  projections of a pair;
* `a3r_inl_sub_inr_mem`: a pair on the diagonal (all `x_k ⊗ 1 - 1 ⊗ x_k` vanish) has equal
  projections;
* `a3r_exists_pair_prime_over`: when the projection is finite, the doubled ring is integral over
  the left copy, so pairs can be specialized along a specialization of the first point (going up).

Source: Stacks Project, Tags 00EA and 00GU (going up for integral extensions); J. Roberts,
*Chow's moving lemma* (1972), proof of the Main Lemma. HC no distance; AV milestone no distance.
-/

noncomputable section

open TensorProduct

namespace HodgeLean.Adapters

/-! ## Two points over the same point -/

/-- Two primes over the same prime are the kernels of two ring maps to a common field that agree
on the base.
Source: Stacks Project, Tag 00EA (the fibre of `Spec(A₁ ⊗_R A₂)` over a pair of points is
`Spec(κ(q₁) ⊗_{κ(p)} κ(q₂))`, a nonzero ring). -/
theorem a3r_exists_common_field {R A₁ A₂ : Type} [CommRing R] [CommRing A₁] [CommRing A₂]
    (φ₁ : R →+* A₁) (φ₂ : R →+* A₂) (q₁ : Ideal A₁) [q₁.IsPrime] (q₂ : Ideal A₂) [q₂.IsPrime]
    (h : q₁.comap φ₁ = q₂.comap φ₂) :
    ∃ (L : Type) (_ : Field L) (ψ₁ : A₁ →+* L) (ψ₂ : A₂ →+* L),
      RingHom.ker ψ₁ = q₁ ∧ RingHom.ker ψ₂ = q₂ ∧ ψ₁.comp φ₁ = ψ₂.comp φ₂ := by
  set p := q₁.comap φ₁
  have hp : p.IsPrime := Ideal.comap_isPrime _ _
  let K := FractionRing (R ⧸ p)
  let K₁ := FractionRing (A₁ ⧸ q₁)
  let K₂ := FractionRing (A₂ ⧸ q₂)
  let f₁ : R ⧸ p →+* A₁ ⧸ q₁ := Ideal.quotientMap q₁ φ₁ le_rfl
  let f₂ : R ⧸ p →+* A₂ ⧸ q₂ := Ideal.quotientMap q₂ φ₂ h.le
  have hf₁ : Function.Injective f₁ := Ideal.quotientMap_injective
  have hf₂ : Function.Injective f₂ := Ideal.quotientMap_injective' h.ge
  let τ₁ : K →+* K₁ := IsLocalization.map K₁ f₁
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f₁ hf₁)
  let τ₂ : K →+* K₂ := IsLocalization.map K₂ f₂
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f₂ hf₂)
  let _ : Algebra K K₁ := τ₁.toAlgebra
  let _ : Algebra K K₂ := τ₂.toAlgebra
  have : Module.Free K K₂ := Module.Free.of_divisionRing K K₂
  have : Module.Flat K K₂ := Module.Flat.of_free
  have : Nontrivial (K₁ ⊗[K] K₂) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right K K₁ K₂ τ₁.injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K₁ ⊗[K] K₂)
  let L := (K₁ ⊗[K] K₂) ⧸ M
  let _ : Field L := Ideal.Quotient.field M
  let ψ₁ : A₁ →+* L := (Ideal.Quotient.mk M).comp ((Algebra.TensorProduct.includeLeftRingHom).comp
    ((algebraMap (A₁ ⧸ q₁) K₁).comp (Ideal.Quotient.mk q₁)))
  let ψ₂ : A₂ →+* L := (Ideal.Quotient.mk M).comp
    ((Algebra.TensorProduct.includeRight : K₂ →ₐ[K] K₁ ⊗[K] K₂).toRingHom.comp
      ((algebraMap (A₂ ⧸ q₂) K₂).comp (Ideal.Quotient.mk q₂)))
  have hker : ∀ {F₁ F₂ : Type} [Field F₁] [Field F₂] (g : F₁ →+* F₂) {A : Type} [CommRing A]
      (q : Ideal A) [q.IsPrime] [Algebra (A ⧸ q) F₁] [IsFractionRing (A ⧸ q) F₁],
      RingHom.ker (g.comp ((algebraMap (A ⧸ q) F₁).comp (Ideal.Quotient.mk q))) = q := by
    intro F₁ F₂ _ _ g A _ q _ _ _
    ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff g g.injective, RingHom.comp_apply,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨L, inferInstance, ψ₁, ψ₂, ?_, ?_, ?_⟩
  · exact hker ((Ideal.Quotient.mk M).comp Algebra.TensorProduct.includeLeftRingHom) q₁
  · exact hker ((Ideal.Quotient.mk M).comp
      (Algebra.TensorProduct.includeRight : K₂ →ₐ[K] K₁ ⊗[K] K₂).toRingHom) q₂
  · ext r
    simp only [ψ₁, ψ₂, RingHom.comp_apply]
    congr 1
    have h₁ : algebraMap (A₁ ⧸ q₁) K₁ (Ideal.Quotient.mk q₁ (φ₁ r)) =
        algebraMap K K₁ (algebraMap (R ⧸ p) K (Ideal.Quotient.mk p r)) := by
      change _ = τ₁ _
      rw [IsLocalization.map_eq]
      rfl
    have h₂ : algebraMap (A₂ ⧸ q₂) K₂ (Ideal.Quotient.mk q₂ (φ₂ r)) =
        algebraMap K K₂ (algebraMap (R ⧸ p) K (Ideal.Quotient.mk p r)) := by
      change _ = τ₂ _
      rw [IsLocalization.map_eq]
      rfl
    change Algebra.TensorProduct.includeLeftRingHom _ = Algebra.TensorProduct.includeRight _
    rw [h₁, h₂]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul _

/-! ## The doubled coordinate ring -/

section Doubled

open MvPolynomial

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

/-- The left copy `ℂ[x_σ] → ℂ[x_σ ⊔ x_σ]`. -/
abbrev a3r_inl : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (σ ⊕ σ) ℂ := rename Sum.inl

/-- The right copy `ℂ[x_σ] → ℂ[x_σ ⊔ x_σ]`. -/
abbrev a3r_inr : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (σ ⊕ σ) ℂ := rename Sum.inr

/-- The diagonal coordinates `x_k ⊗ 1 - 1 ⊗ x_k`. -/
abbrev a3r_δ (k : σ) : MvPolynomial (σ ⊕ σ) ℂ := X (Sum.inl k) - X (Sum.inr k)

/-- The ideal of `V(I) ×_{ℙⁿ} V(I)` in the doubled ring: both copies lie in `V(I)` and the two
projections by `ℓ` agree. -/
def a3r_pairIdeal (I : Ideal (MvPolynomial σ ℂ)) (ℓ : Matrix ρ σ ℂ) :
    Ideal (MvPolynomial (σ ⊕ σ) ℂ) :=
  I.map a3r_inl ⊔ I.map a3r_inr ⊔
    Ideal.span (Set.range fun i => a3r_inl (a3r_lin ℓ (X i)) - a3r_inr (a3r_lin ℓ (X i)))

omit [Fintype σ] in
/-- An ideal containing the differences `x_k ⊗ 1 - 1 ⊗ x_k` contains `F ⊗ 1 - 1 ⊗ F` for every
`F`. -/
theorem a3r_inl_sub_inr_mem (𝔔 : Ideal (MvPolynomial (σ ⊕ σ) ℂ)) (h : ∀ k, a3r_δ k ∈ 𝔔)
    (F : MvPolynomial σ ℂ) : a3r_inl F - a3r_inr F ∈ 𝔔 := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG =>
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem hF hG
  | mul_X F k hF =>
    rw [map_mul, map_mul, rename_X, rename_X,
      show a3r_inl F * X (Sum.inl k) - a3r_inr F * X (Sum.inr k) =
        (a3r_inl F - a3r_inr F) * X (Sum.inl k) + a3r_inr F * a3r_δ k by ring]
    exact add_mem (𝔔.mul_mem_right _ hF) (𝔔.mul_mem_left _ (h k))

omit [Fintype ρ] in
/-- The two projections of a pair in `a3r_pairIdeal` agree on all of `ℂ[ℓ]`. -/
theorem a3r_inl_lin_sub_inr_lin_mem (I : Ideal (MvPolynomial σ ℂ)) (ℓ : Matrix ρ σ ℂ)
    (F : MvPolynomial ρ ℂ) :
    a3r_inl (a3r_lin ℓ F) - a3r_inr (a3r_lin ℓ F) ∈ a3r_pairIdeal I ℓ := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG =>
    rw [map_add, map_add, map_add, add_sub_add_comm]
    exact add_mem hF hG
  | mul_X F i hF =>
    rw [map_mul, map_mul, map_mul,
      show a3r_inl (a3r_lin ℓ F) * a3r_inl (a3r_lin ℓ (X i)) -
          a3r_inr (a3r_lin ℓ F) * a3r_inr (a3r_lin ℓ (X i)) =
        (a3r_inl (a3r_lin ℓ F) - a3r_inr (a3r_lin ℓ F)) * a3r_inl (a3r_lin ℓ (X i)) +
          a3r_inr (a3r_lin ℓ F) * (a3r_inl (a3r_lin ℓ (X i)) - a3r_inr (a3r_lin ℓ (X i))) by ring]
    refine add_mem (Ideal.mul_mem_right _ _ hF) (Ideal.mul_mem_left _ _ ?_)
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)

omit [Fintype ρ] in
/-- Two primes containing `I` with the same image under the projection are the two contractions
of a prime of the doubled ring containing `a3r_pairIdeal I ℓ`. -/
theorem a3r_exists_pair_prime (I : Ideal (MvPolynomial σ ℂ)) (ℓ : Matrix ρ σ ℂ)
    (Q₁ Q₂ : Ideal (MvPolynomial σ ℂ)) [Q₁.IsPrime] [Q₂.IsPrime] (h₁ : I ≤ Q₁) (h₂ : I ≤ Q₂)
    (h : Q₁.comap (a3r_lin ℓ) = Q₂.comap (a3r_lin ℓ)) :
    ∃ 𝔔 : Ideal (MvPolynomial (σ ⊕ σ) ℂ), 𝔔.IsPrime ∧ a3r_pairIdeal I ℓ ≤ 𝔔 ∧
      𝔔.comap a3r_inl = Q₁ ∧ 𝔔.comap a3r_inr = Q₂ := by
  obtain ⟨L, _, ψ₁, ψ₂, hk₁, hk₂, hψ⟩ := a3r_exists_common_field (a3r_lin ℓ).toRingHom
    (a3r_lin ℓ).toRingHom Q₁ Q₂ h
  have hC : ∀ c : ℂ, ψ₁ (C c) = ψ₂ (C c) := by
    intro c
    have := congrArg (fun φ : MvPolynomial ρ ℂ →+* L => φ (C c)) hψ
    simpa [a3r_lin_C] using this
  let Ψ : MvPolynomial (σ ⊕ σ) ℂ →+* L :=
    eval₂Hom (ψ₁.comp C) (Sum.elim (fun k => ψ₁ (X k)) (fun k => ψ₂ (X k)))
  have hΨ₁ : Ψ.comp (a3r_inl : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom = ψ₁ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun k => ?_)
    · simp [Ψ]
    · simp [Ψ]
  have hΨ₂ : Ψ.comp (a3r_inr : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun k => ?_)
    · simp [Ψ, hC]
    · simp [Ψ]
  have hΨ₁' : ∀ F, Ψ (a3r_inl F) = ψ₁ F := fun F =>
    congrArg (fun φ : MvPolynomial σ ℂ →+* L => φ F) hΨ₁
  have hΨ₂' : ∀ F, Ψ (a3r_inr F) = ψ₂ F := fun F =>
    congrArg (fun φ : MvPolynomial σ ℂ →+* L => φ F) hΨ₂
  refine ⟨RingHom.ker Ψ, RingHom.ker_isPrime Ψ, ?_, ?_, ?_⟩
  · refine sup_le (sup_le ?_ ?_) (Ideal.span_le.2 ?_)
    · refine Ideal.map_le_iff_le_comap.2 fun F hF => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, hΨ₁', ← RingHom.mem_ker, hk₁]
      exact h₁ hF
    · refine Ideal.map_le_iff_le_comap.2 fun F hF => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, hΨ₂', ← RingHom.mem_ker, hk₂]
      exact h₂ hF
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hΨ₁', hΨ₂', sub_eq_zero]
      exact congrArg (fun φ : MvPolynomial ρ ℂ →+* L => φ (X i)) hψ
  · ext F
    rw [Ideal.mem_comap, RingHom.mem_ker, hΨ₁', ← RingHom.mem_ker, hk₁]
  · ext F
    rw [Ideal.mem_comap, RingHom.mem_ker, hΨ₂', ← RingHom.mem_ker, hk₂]

omit [Fintype ρ] in
theorem a3r_map_inl_le (I : Ideal (MvPolynomial σ ℂ)) (ℓ : Matrix ρ σ ℂ) :
    I.map a3r_inl ≤ a3r_pairIdeal I ℓ :=
  le_sup_left.trans le_sup_left

omit [Fintype ρ] in
theorem a3r_map_inr_le (I : Ideal (MvPolynomial σ ℂ)) (ℓ : Matrix ρ σ ℂ) :
    I.map a3r_inr ≤ a3r_pairIdeal I ℓ :=
  le_sup_right.trans le_sup_left

omit [Fintype ρ] in
/-- Going up in the doubled ring: when `ℂ[x]/I` is finite over `ℂ[ℓ]`, the doubled ring modulo
`a3r_pairIdeal I ℓ` is integral over the left copy, so a prime over `𝔔 ∩ ℂ[x] ⊆ Y` exists above
any prime `𝔔`. -/
theorem a3r_exists_pair_prime_over (I : Ideal (MvPolynomial σ ℂ)) (ℓ : Matrix ρ σ ℂ)
    (hfin : ((Ideal.Quotient.mk I).comp (a3r_lin ℓ).toRingHom).Finite)
    (𝔔 : Ideal (MvPolynomial (σ ⊕ σ) ℂ)) [𝔔.IsPrime] (h𝔔 : a3r_pairIdeal I ℓ ≤ 𝔔)
    (Y : Ideal (MvPolynomial σ ℂ)) [Y.IsPrime] (hY : 𝔔.comap a3r_inl ≤ Y) :
    ∃ 𝔔' : Ideal (MvPolynomial (σ ⊕ σ) ℂ), 𝔔'.IsPrime ∧ 𝔔 ≤ 𝔔' ∧ 𝔔'.comap a3r_inl = Y := by
  classical
  set J := a3r_pairIdeal I ℓ
  set A := MvPolynomial σ ℂ ⧸ I
  set Tb := MvPolynomial (σ ⊕ σ) ℂ ⧸ J
  have hIl : I ≤ J.comap (a3r_inl : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom :=
    Ideal.map_le_iff_le_comap.1 (a3r_map_inl_le I ℓ)
  have hIr : I ≤ J.comap (a3r_inr : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom :=
    Ideal.map_le_iff_le_comap.1 (a3r_map_inr_le I ℓ)
  let left : A →+* Tb := Ideal.quotientMap J (a3r_inl : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom hIl
  let right : A →+* Tb := Ideal.quotientMap J (a3r_inr : MvPolynomial σ ℂ →ₐ[ℂ] _).toRingHom hIr
  let φ : MvPolynomial ρ ℂ →+* A := (Ideal.Quotient.mk I).comp (a3r_lin ℓ).toRingHom
  have hφ : right.comp φ = left.comp φ := by
    ext F
    · simp only [RingHom.comp_apply, φ, left, right]
      exact (Ideal.Quotient.eq.2 (a3r_inl_lin_sub_inr_lin_mem I ℓ (C _))).symm
    · simp only [RingHom.comp_apply, φ, left, right]
      exact (Ideal.Quotient.eq.2 (a3r_inl_lin_sub_inr_lin_mem I ℓ (X _))).symm
  let _ : Algebra A Tb := left.toAlgebra
  have hint : ∀ a : A, IsIntegral A (right a) := by
    intro a
    obtain ⟨p, hpm, hp⟩ := hfin.to_isIntegral a
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ (left.comp φ) (right a) p = 0
    rw [← hφ, ← Polynomial.hom_eval₂, hp, map_zero]
  have hintT : ∀ F : MvPolynomial (σ ⊕ σ) ℂ, IsIntegral A (Ideal.Quotient.mk J F) := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C c =>
      have : Ideal.Quotient.mk J (C c) = algebraMap A Tb (Ideal.Quotient.mk I (C c)) := by
        change _ = left _
        rw [Ideal.quotientMap_mk]
        simp
      rw [this]
      exact isIntegral_algebraMap
    | add F G hF hG => rw [map_add]; exact hF.add hG
    | mul_X F k hF =>
      rw [map_mul]
      refine hF.mul ?_
      rcases k with k | k
      · have : Ideal.Quotient.mk J (X (Sum.inl k)) = algebraMap A Tb (Ideal.Quotient.mk I (X k)) := by
          change _ = left _
          rw [Ideal.quotientMap_mk]
          simp
        rw [this]
        exact isIntegral_algebraMap
      · have : Ideal.Quotient.mk J (X (Sum.inr k)) = right (Ideal.Quotient.mk I (X k)) := by
          rw [Ideal.quotientMap_mk]
          simp
        rw [this]
        exact hint _
  have : Algebra.IsIntegral A Tb := ⟨fun x => by
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hintT F⟩
  -- going up
  have hIY : I ≤ Y := by
    intro F hF
    apply hY
    rw [Ideal.mem_comap]
    exact h𝔔 (a3r_map_inl_le I ℓ (Ideal.mem_map_of_mem _ hF))
  have hkerY : RingHom.ker (Ideal.Quotient.mk I) ≤ Y := by rwa [Ideal.mk_ker]
  have hkerQ : RingHom.ker (Ideal.Quotient.mk J) ≤ 𝔔 := by rwa [Ideal.mk_ker]
  set P := Y.map (Ideal.Quotient.mk I)
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerY
  set Qb := 𝔔.map (Ideal.Quotient.mk J)
  have hcomapP : P.comap (Ideal.Quotient.mk I) = Y := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hkerY]
  have hcomapQ : Qb.comap (Ideal.Quotient.mk J) = 𝔔 := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hkerQ]
  have hunder : Ideal.under A Qb ≤ P := by
    intro a ha
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.under, Ideal.mem_comap] at ha
    change left (Ideal.Quotient.mk I F) ∈ Qb at ha
    rw [Ideal.quotientMap_mk, ← Ideal.mem_comap, hcomapQ] at ha
    exact Ideal.mem_map_of_mem _ (hY ha)
  obtain ⟨Qb', hle, hQb', hover⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P Qb hunder
  refine ⟨Qb'.comap (Ideal.Quotient.mk J), Ideal.comap_isPrime _ _, ?_, ?_⟩
  · rw [← hcomapQ]
    exact Ideal.comap_mono hle
  · ext F
    rw [Ideal.mem_comap, Ideal.mem_comap]
    rw [← hcomapP, Ideal.mem_comap, ← hover, Ideal.under, Ideal.mem_comap]
    rfl

end Doubled

end HodgeLean.Adapters

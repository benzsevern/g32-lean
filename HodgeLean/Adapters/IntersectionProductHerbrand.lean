import HodgeLean.Adapters.IntersectionProductCMTor

/-! # Herbrand differences and the Euler characteristic of `Tor` along a nonzerodivisor

For `r ∈ R` and an `R`-module `M`, the Herbrand difference is
`e_r(M) = length (M ⧸ r M) − length (0 :_M r)`. This file proves:
* lengths along a six-term exact sequence: `ℓ K₁ + ℓ K₃ + ℓ C₂ = ℓ K₂ + ℓ C₁ + ℓ C₃`
  (`a3e_length_six`);
* additivity of the Herbrand difference along short exact sequences, from the snake lemma
  (`a3e_length_herbrand_ses`);
* vanishing of the Herbrand difference on modules of finite length (`a3e_herbrand_finiteLength`);
* the Euler characteristic of `Tor(-, N)` along a nonzerodivisor `r` on `M`:
  `Σ (-1)^i ℓ Tor_i(M ⧸ r M, N) = Σ (-1)^i e_r(Tor_i(M, N))` (`a3e_euler_tor`), from the long
  exact sequence of `Tor` attached to `0 → M →r M → M ⧸ r M → 0`.

These are the bookkeeping steps of Serre's computation of the intersection multiplicity of a
principal divisor with a properly meeting subvariety.

Source: Serre, *Algèbre locale, multiplicités*, Chapitre I, §2 and Chapitre V, B.2
(additivity of Euler–Poincaré characteristics); Fulton, *Intersection Theory*, second edition,
Lemma A.2.1 and Example A.2.1 (the Herbrand quotient `e_M(r)`).
HC no distance; AV milestone no distance.
-/

open CategoryTheory CategoryTheory.Limits Pointwise

noncomputable section
namespace HodgeLean.Adapters
universe u v

section lengths
variable {R : Type u} [CommRing R]

/-- The length of `M` is the length of the kernel plus the length of the image. -/
theorem a3e_length_eq_ker_add_range {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) :
    Module.length R M = Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range f) :=
  Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
    (Submodule.injective_subtype _) f.surjective_rangeRestrict (by
      intro x
      simp [LinearMap.rangeRestrict, Subtype.ext_iff])

/-- Along an exact pair, the kernel of the second map and the image of the first have equal
length. -/
theorem a3e_length_ker_eq_range {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) :
    Module.length R (LinearMap.ker g) = Module.length R (LinearMap.range f) := by
  rw [LinearMap.exact_iff.mp h]

/-- Lengths along a six-term exact sequence `0 → K₁ → K₂ → K₃ → C₁ → C₂ → C₃ → 0`. -/
theorem a3e_length_six {K₁ K₂ K₃ C₁ C₂ C₃ : Type*} [AddCommGroup K₁] [Module R K₁]
    [AddCommGroup K₂] [Module R K₂] [AddCommGroup K₃] [Module R K₃] [AddCommGroup C₁]
    [Module R C₁] [AddCommGroup C₂] [Module R C₂] [AddCommGroup C₃] [Module R C₃]
    (f₁ : K₁ →ₗ[R] K₂) (f₂ : K₂ →ₗ[R] K₃) (δ : K₃ →ₗ[R] C₁) (g₁ : C₁ →ₗ[R] C₂)
    (g₂ : C₂ →ₗ[R] C₃) (hf₁ : Function.Injective f₁) (h₂ : Function.Exact f₁ f₂)
    (h₃ : Function.Exact f₂ δ) (h₄ : Function.Exact δ g₁) (h₅ : Function.Exact g₁ g₂)
    (hg₂ : Function.Surjective g₂) :
    Module.length R K₁ + Module.length R K₃ + Module.length R C₂ =
      Module.length R K₂ + Module.length R C₁ + Module.length R C₃ := by
  have e₁ := a3e_length_eq_ker_add_range f₁
  have e₂ := a3e_length_eq_ker_add_range f₂
  have e₃ := a3e_length_eq_ker_add_range δ
  have e₄ := a3e_length_eq_ker_add_range g₁
  have e₅ := a3e_length_eq_ker_add_range g₂
  rw [LinearMap.ker_eq_bot.mpr hf₁, Module.length_bot, zero_add] at e₁
  rw [a3e_length_ker_eq_range h₂] at e₂
  rw [a3e_length_ker_eq_range h₃] at e₃
  rw [a3e_length_ker_eq_range h₄] at e₄
  rw [a3e_length_ker_eq_range h₅, LinearMap.range_eq_top.mpr hg₂, Module.length_top] at e₅
  rw [e₁, e₂, e₃, e₄, e₅]
  ring

end lengths

section herbrand
variable {R : Type u} [CommRing R]

/-- The kernel `0 :_M r` of multiplication by `r`.
Source: Fulton, *Intersection Theory*, second edition, Example A.2.1 (the module `₍r₎M`). -/
abbrev a3e_kerSMul (r : R) (M : Type*) [AddCommGroup M] [Module R M] : Submodule R M :=
  LinearMap.ker (LinearMap.lsmul R M r)

example (M : Type*) [AddCommGroup M] [Module R M] : a3e_kerSMul (0 : R) M = ⊤ := by
  ext x
  simp

/-- The Herbrand difference `e_r(M) = length (M ⧸ r M) − length (0 :_M r)`, as an integer (each
length read through `ENat.toNat`).
Source: Fulton, *Intersection Theory*, second edition, Example A.2.1 (`e_M(r)`); Serre,
*Algèbre locale, multiplicités*, Chapitre I, §2. -/
def a3e_herbrand (r : R) (M : Type*) [AddCommGroup M] [Module R M] : ℤ :=
  ((Module.length R (QuotSMulTop r M)).toNat : ℤ) - ((Module.length R (a3e_kerSMul r M)).toNat : ℤ)

example (r : R) : a3e_herbrand r (PUnit : Type) = 0 := by
  simp [a3e_herbrand, Module.length_eq_zero]

variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]

/-- The restriction of a linear map to the kernels of multiplication by `r`.
Source: Mathlib, `LinearMap.restrict`; the left column of the snake lemma (Weibel,
*An Introduction to Homological Algebra*, Lemma 1.3.2). -/
def a3e_kerMap (r : R) (f : M₁ →ₗ[R] M₂) : a3e_kerSMul r M₁ →ₗ[R] a3e_kerSMul r M₂ :=
  f.restrict fun x hx => by
    simp only [LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
    rw [← map_smul, hx, map_zero]

example (r : R) (f : M₁ →ₗ[R] M₂) (x : a3e_kerSMul r M₁) : (a3e_kerMap r f x : M₂) = f x := rfl

/-- The map induced by a linear map on the quotients by `r`.
Source: Mathlib, `QuotSMulTop.map`; the right column of the snake lemma (Weibel,
*An Introduction to Homological Algebra*, Lemma 1.3.2). -/
def a3e_quotMap (r : R) (f : M₁ →ₗ[R] M₂) : QuotSMulTop r M₁ →ₗ[R] QuotSMulTop r M₂ :=
  QuotSMulTop.map r f

example (r : R) : a3e_quotMap r (LinearMap.id : M₁ →ₗ[R] M₁) = LinearMap.id :=
  QuotSMulTop.map_id r M₁

theorem a3e_quotMap_mk (r : R) (f : M₁ →ₗ[R] M₂) (x : M₁) :
    a3e_quotMap r f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

theorem a3e_exact_kerSMul (r : R) (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Exact (a3e_kerSMul r M).subtype (LinearMap.lsmul R M r) := fun x => by
  simp

theorem a3e_lsmul_comm (r : R) (f : M₁ →ₗ[R] M₂) :
    f ∘ₗ LinearMap.lsmul R M₁ r = LinearMap.lsmul R M₂ r ∘ₗ f := by
  ext x
  simp

/-- The Herbrand difference along a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, in lengths:
the snake lemma for multiplication by `r` gives the exact sequence
`0 → K₁ → K₂ → K₃ → C₁ → C₂ → C₃ → 0` of kernels and cokernels. -/
theorem a3e_length_herbrand_ses (r : R) (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.length R (a3e_kerSMul r M₁) + Module.length R (a3e_kerSMul r M₃) +
        Module.length R (QuotSMulTop r M₂) =
      Module.length R (a3e_kerSMul r M₂) + Module.length R (QuotSMulTop r M₁) +
        Module.length R (QuotSMulTop r M₃) := by
  refine a3e_length_six (a3e_kerMap r f) (a3e_kerMap r g)
    (SnakeLemma.δ' (LinearMap.lsmul R M₁ r) (LinearMap.lsmul R M₂ r) (LinearMap.lsmul R M₃ r)
      f g hfg f g hfg (a3e_lsmul_comm r f) (a3e_lsmul_comm r g) (a3e_kerSMul r M₃).subtype
      (a3e_exact_kerSMul r M₃) (r • (⊤ : Submodule R M₁)).mkQ (LinearMap.exact_lsmul_mkQ_smul_top M₁ r) hg hf)
    (a3e_quotMap r f) (a3e_quotMap r g) ?_ ?_ ?_ ?_ (QuotSMulTop.map_exact r hfg hg)
    (QuotSMulTop.map_surjective r hg)
  · intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  · intro x
    constructor
    · intro hx
      have hx' : g x.1 = 0 := congrArg Subtype.val hx
      obtain ⟨y, hy⟩ := (hfg x.1).mp hx'
      refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
      have : f (r • y) = 0 := by
        rw [map_smul, hy]
        exact x.2
      simpa using hf (this.trans (map_zero f).symm)
    · rintro ⟨y, rfl⟩
      exact Subtype.ext (hfg.apply_apply_eq_zero y.1)
  · apply SnakeLemma.exact_δ'_right (ι₂ := (a3e_kerSMul r M₂).subtype)
      (hι₂ := a3e_exact_kerSMul r M₂) (F := a3e_kerMap r g) (hF := rfl)
      (h := Submodule.injective_subtype _)
  · apply SnakeLemma.exact_δ'_left (π₂ := (r • (⊤ : Submodule R M₂)).mkQ)
      (hπ₂ := LinearMap.exact_lsmul_mkQ_smul_top M₂ r)
      (G := a3e_quotMap r f) (hF := rfl) (h := Submodule.mkQ_surjective _)

/-- The Herbrand difference is additive along short exact sequences whose kernels and cokernels
of `r` have finite length. -/
theorem a3e_herbrand_ses (r : R) (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hK₁ : Module.length R (a3e_kerSMul r M₁) ≠ ⊤) (hK₂ : Module.length R (a3e_kerSMul r M₂) ≠ ⊤)
    (hK₃ : Module.length R (a3e_kerSMul r M₃) ≠ ⊤) (hC₁ : Module.length R (QuotSMulTop r M₁) ≠ ⊤)
    (hC₂ : Module.length R (QuotSMulTop r M₂) ≠ ⊤)
    (hC₃ : Module.length R (QuotSMulTop r M₃) ≠ ⊤) :
    a3e_herbrand r M₂ = a3e_herbrand r M₁ + a3e_herbrand r M₃ := by
  have h := a3e_length_herbrand_ses r f g hf hg hfg
  unfold a3e_herbrand
  generalize Module.length R (a3e_kerSMul r M₁) = a₁ at h hK₁ ⊢
  generalize Module.length R (a3e_kerSMul r M₂) = a₂ at h hK₂ ⊢
  generalize Module.length R (a3e_kerSMul r M₃) = a₃ at h hK₃ ⊢
  generalize Module.length R (QuotSMulTop r M₁) = b₁ at h hC₁ ⊢
  generalize Module.length R (QuotSMulTop r M₂) = b₂ at h hC₂ ⊢
  generalize Module.length R (QuotSMulTop r M₃) = b₃ at h hC₃ ⊢
  lift a₁ to ℕ using hK₁
  lift a₂ to ℕ using hK₂
  lift a₃ to ℕ using hK₃
  lift b₁ to ℕ using hC₁
  lift b₂ to ℕ using hC₂
  lift b₃ to ℕ using hC₃
  norm_cast at h
  simp only [ENat.toNat_natCast]
  omega

/-- The Herbrand difference of a module of finite length is zero. -/
theorem a3e_herbrand_finiteLength (r : R) (M : Type*) [AddCommGroup M] [Module R M]
    (hM : Module.length R M ≠ ⊤) : a3e_herbrand r M = 0 := by
  have e₁ := a3e_length_eq_ker_add_range (LinearMap.lsmul R M r)
  have e₂ := a3e_length_eq_ker_add_range (r • (⊤ : Submodule R M)).mkQ
  rw [Submodule.ker_mkQ, Submodule.range_mkQ, Module.length_top] at e₂
  have hr : LinearMap.range (LinearMap.lsmul R M r) = r • (⊤ : Submodule R M) := by
    ext x
    simp [Submodule.mem_smul_pointwise_iff_exists, eq_comm]
  rw [hr] at e₁
  have hK : Module.length R (a3e_kerSMul r M) ≠ ⊤ := fun h => hM (by rw [e₁, h, top_add])
  have hS : Module.length R ↥(r • (⊤ : Submodule R M)) ≠ ⊤ := fun h => hM (by rw [e₁, h, add_top])
  have hC : Module.length R (QuotSMulTop r M) ≠ ⊤ := fun h => hM (by rw [e₂, h, add_top])
  unfold a3e_herbrand
  generalize Module.length R M = m at e₁ e₂ hM
  generalize Module.length R (a3e_kerSMul r M) = a at e₁ hK ⊢
  generalize Module.length R ↥(r • (⊤ : Submodule R M)) = b at e₁ e₂ hS
  generalize Module.length R (QuotSMulTop r M) = c at e₂ hC ⊢
  lift a to ℕ using hK
  lift b to ℕ using hS
  lift c to ℕ using hC
  subst e₁
  norm_cast at e₂
  simp only [ENat.toNat_natCast]
  omega

end herbrand

section euler
variable {R : Type u} [CommRing R]

theorem a3e_range_lsmul (r : R) (M : Type*) [AddCommGroup M] [Module R M] :
    LinearMap.range (LinearMap.lsmul R M r) = r • (⊤ : Submodule R M) := by
  ext x
  simp [Submodule.mem_smul_pointwise_iff_exists, eq_comm]

/-- Length of the middle term of `H →r H → L → H' →r H'`: `ℓ L = ℓ (H ⧸ r H) + ℓ (0 :_{H'} r)`. -/
theorem a3e_length_mid (r : R) {H L H' : Type*} [AddCommGroup H] [Module R H] [AddCommGroup L]
    [Module R L] [AddCommGroup H'] [Module R H'] (g : H →ₗ[R] L) (δ : L →ₗ[R] H')
    (h₁ : LinearMap.ker g = r • (⊤ : Submodule R H)) (h₂ : LinearMap.range g = LinearMap.ker δ)
    (h₃ : LinearMap.range δ = a3e_kerSMul r H') :
    Module.length R L = Module.length R (QuotSMulTop r H) + Module.length R (a3e_kerSMul r H') := by
  rw [a3e_length_eq_ker_add_range δ, ← h₂, h₃,
    ← (g.quotKerEquivRange).length_eq, (Submodule.quotEquivOfEq _ _ h₁).length_eq]

/-- Length of the last term of `H →r H → L → 0`: `ℓ L = ℓ (H ⧸ r H)`. -/
theorem a3e_length_last (r : R) {H L : Type*} [AddCommGroup H] [Module R H] [AddCommGroup L]
    [Module R L] (g : H →ₗ[R] L) (h₁ : LinearMap.ker g = r • (⊤ : Submodule R H))
    (hg : Function.Surjective g) :
    Module.length R L = Module.length R (QuotSMulTop r H) := by
  rw [← (LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hg)).length_eq,
    ← (g.quotKerEquivRange).length_eq, (Submodule.quotEquivOfEq _ _ h₁).length_eq]

/-- The alternating sum along `L₀ = C₀`, `L_{i+1} = C_{i+1} + K_i`. -/
theorem a3e_alt_sum (L C K : ℕ → ℤ) (m : ℕ) (h0 : L 0 = C 0)
    (hs : ∀ i, i < m → L (i + 1) = C (i + 1) + K i) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i * L i =
      ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i * (C i - K i) + (-1) ^ m * K m := by
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (fun i hi => hs i (by omega)),
      Finset.sum_range_succ (n := m + 1), hs m (by omega)]
    ring

theorem a3e_length_kerSMul_congr (r : R) {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') :
    Module.length R (a3e_kerSMul r M) = Module.length R (a3e_kerSMul r M') := by
  have h : (a3e_kerSMul r M).map (e : M →ₗ[R] M') = a3e_kerSMul r M' := by
    ext y
    simp only [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.lsmul_apply]
    constructor
    · intro hy
      rw [← e.apply_symm_apply y, ← map_smul, hy, map_zero]
    · intro hy
      rw [← map_smul, hy, map_zero]
  exact (e.ofSubmodules _ _ h).length_eq

/-- The Herbrand difference is invariant under linear equivalence. -/
theorem a3e_herbrand_congr (r : R) {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') : a3e_herbrand r M = a3e_herbrand r M' := by
  unfold a3e_herbrand
  rw [(QuotSMulTop.congr r e).length_eq, a3e_length_kerSMul_congr r e]

end euler

section torEuler
variable {R : Type u} [CommRing R]
open MonoidalCategory

variable {M : ModuleCat.{u} R} {r : R} (hr : IsSMulRegular M r) {N : ModuleCat.{u} R}
  (Q : ProjectiveResolution N)

theorem a3e_homologyMap_smul_hom (X : ModuleCat.{u} R) (r : R) (i : ℕ) :
    (HomologicalComplex.homologyMap (a3c_tensMap (r • 𝟙 X) Q.complex) i).hom =
      LinearMap.lsmul R ((a3c_tensC X Q.complex).homology i) r := by
  rw [a3c_homologyMap_tensMap_smul]
  ext x
  simp

include hr in
theorem a3e_ker_homologyMap_g (i : ℕ) :
    LinearMap.ker
        (HomologicalComplex.homologyMap (a3c_tensMap (M.smulShortComplex r).g Q.complex) i).hom =
      r • (⊤ : Submodule R ((a3c_tensC M Q.complex).homology i)) := by
  have := ((a3c_sesC_shortExact _ hr.smulShortComplex_shortExact Q.complex
    Q.projective).homology_exact₂ i).moduleCat_range_eq_ker
  rw [← a3e_range_lsmul]
  refine this.symm.trans ?_
  exact congrArg LinearMap.range (a3e_homologyMap_smul_hom Q M r i)

instance a3e_epi_whiskerRight {X Y : ModuleCat.{u} R} (f : X ⟶ Y) [Epi f] (Z : ModuleCat.{u} R) :
    Epi (f ▷ Z) := by
  have h : f ▷ Z = (β_ X Z).hom ≫ Z ◁ f ≫ (β_ Y Z).inv := by
    rw [← BraidedCategory.braiding_naturality_left_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

theorem a3e_surjective_homologyMap_g_zero :
    Function.Surjective
      (HomologicalComplex.homologyMap (a3c_tensMap (M.smulShortComplex r).g Q.complex) 0).hom := by
  rw [← ModuleCat.epi_iff_surjective]
  have h := a3c_H0Iso_naturality Q (M.smulShortComplex r).g
  rw [← Iso.eq_comp_inv, Category.assoc] at h
  rw [h]
  infer_instance

include hr in
/-- `ℓ H_0(M/rM ⊗ Q) = ℓ (H_0(M ⊗ Q) ⧸ r)`. -/
theorem a3e_length_homology_zero :
    Module.length R ((a3c_tensC (ModuleCat.of R (QuotSMulTop r M)) Q.complex).homology 0) =
      Module.length R (QuotSMulTop r ((a3c_tensC M Q.complex).homology 0)) :=
  a3e_length_last r _ (a3e_ker_homologyMap_g hr Q 0) (a3e_surjective_homologyMap_g_zero Q)

include hr in
/-- `ℓ H_{i+1}(M/rM ⊗ Q) = ℓ (H_{i+1}(M ⊗ Q) ⧸ r) + ℓ (0 :_{H_i(M ⊗ Q)} r)`. -/
theorem a3e_length_homology_succ (i : ℕ) :
    Module.length R ((a3c_tensC (ModuleCat.of R (QuotSMulTop r M)) Q.complex).homology (i + 1)) =
      Module.length R (QuotSMulTop r ((a3c_tensC M Q.complex).homology (i + 1))) +
        Module.length R (a3e_kerSMul r ((a3c_tensC M Q.complex).homology i)) := by
  have hT := a3c_sesC_shortExact _ hr.smulShortComplex_shortExact Q.complex Q.projective
  refine a3e_length_mid r _ (hT.δ (i + 1) i (by simp)).hom (a3e_ker_homologyMap_g hr Q (i + 1))
    (hT.homology_exact₃ (i + 1) i (by simp)).moduleCat_range_eq_ker ?_
  refine (hT.homology_exact₁ (i + 1) i (by simp)).moduleCat_range_eq_ker.trans ?_
  exact congrArg LinearMap.ker (a3e_homologyMap_smul_hom Q M r i)

include hr in
/-- If `H_{m+1}(M/rM ⊗ Q) = 0`, multiplication by `r` is injective on `H_m(M ⊗ Q)`. -/
theorem a3e_length_kerSMul_top (m : ℕ)
    (htop : IsZero ((a3c_tensC (ModuleCat.of R (QuotSMulTop r M)) Q.complex).homology (m + 1))) :
    Module.length R (a3e_kerSMul r ((a3c_tensC M Q.complex).homology m)) = 0 := by
  have hT := a3c_sesC_shortExact _ hr.smulShortComplex_shortExact Q.complex Q.projective
  have h₁ := (hT.homology_exact₁ (m + 1) m (by simp)).moduleCat_range_eq_ker
  have hδ : hT.δ (m + 1) m (by simp) = 0 := htop.eq_of_src _ _
  rw [Module.length_eq_zero_iff, Submodule.subsingleton_iff_eq_bot]
  have h₂ : LinearMap.ker (LinearMap.lsmul R ((a3c_tensC M Q.complex).homology m) r) =
      LinearMap.range (hT.δ (m + 1) m (by simp)).hom :=
    (congrArg LinearMap.ker (a3e_homologyMap_smul_hom Q M r m)).symm.trans h₁.symm
  change LinearMap.ker (LinearMap.lsmul R _ r) = ⊥
  rw [h₂, hδ, ModuleCat.hom_zero, LinearMap.range_zero]
  rfl

/-- The Euler characteristic of `Tor(-, N)` along a nonzerodivisor: if `r` is regular on `M`,
the kernels and cokernels of `r` on `Tor_i(M, N)` have finite length for `i ≤ m`, and
`Tor_{m+1}(M ⧸ r M, N) = 0`, then
`Σ_{i ≤ m} (-1)^i ℓ Tor_i(M ⧸ r M, N) = Σ_{i ≤ m} (-1)^i e_r(Tor_i(M, N))`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.2 (the exact sequence of `Tor`
attached to `0 → M →r M → M/rM → 0`) and Chapitre I, §2 (Herbrand differences); Fulton,
*Intersection Theory*, second edition, Example A.2.1. -/
theorem a3e_euler_tor (M N : ModuleCat.{u} R) (r : R) (hr : IsSMulRegular M r) (m : ℕ)
    (hK : ∀ i ≤ m, Module.length R (a3e_kerSMul r (((Tor (ModuleCat.{u} R) i).obj M).obj N)) ≠ ⊤)
    (hC : ∀ i ≤ m, Module.length R (QuotSMulTop r (((Tor (ModuleCat.{u} R) i).obj M).obj N)) ≠ ⊤)
    (htop : IsZero (((Tor (ModuleCat.{u} R) (m + 1)).obj
      (ModuleCat.of R (QuotSMulTop r M))).obj N)) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i * ((Module.length R (((Tor (ModuleCat.{u} R) i).obj
        (ModuleCat.of R (QuotSMulTop r M))).obj N)).toNat : ℤ) =
      ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        a3e_herbrand r (((Tor (ModuleCat.{u} R) i).obj M).obj N) := by
  let Q := ProjectiveResolution.of N
  have eM := fun i => (a3c_torIso M N Q i).toLinearEquiv
  have eQ := fun i => (a3c_torIso (ModuleCat.of R (QuotSMulTop r M)) N Q i).toLinearEquiv
  have hK' : ∀ i ≤ m, Module.length R (a3e_kerSMul r ((a3c_tensC M Q.complex).homology i)) ≠ ⊤ :=
    fun i hi => by rw [← a3e_length_kerSMul_congr r (eM i)]; exact hK i hi
  have hC' : ∀ i ≤ m, Module.length R (QuotSMulTop r ((a3c_tensC M Q.complex).homology i)) ≠ ⊤ :=
    fun i hi => by rw [← (QuotSMulTop.congr r (eM i)).length_eq]; exact hC i hi
  have hKm := a3e_length_kerSMul_top hr Q m
    (htop.of_iso (a3c_torIso (ModuleCat.of R (QuotSMulTop r M)) N Q (m + 1)).symm)
  have key := a3e_alt_sum
    (fun i => ((Module.length R ((a3c_tensC (ModuleCat.of R (QuotSMulTop r M))
      Q.complex).homology i)).toNat : ℤ))
    (fun i => ((Module.length R (QuotSMulTop r ((a3c_tensC M Q.complex).homology i))).toNat : ℤ))
    (fun i => ((Module.length R (a3e_kerSMul r ((a3c_tensC M Q.complex).homology i))).toNat : ℤ))
    m (by simp only [a3e_length_homology_zero hr Q])
    (fun i hi => by
      simp only [a3e_length_homology_succ hr Q i]
      rw [ENat.toNat_add (hC' (i + 1) (by omega)) (hK' i (by omega))]
      push_cast
      rfl)
  simp only [hKm, ENat.toNat_zero, Nat.cast_zero, mul_zero, add_zero] at key
  simp only [(eQ _).length_eq]
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [a3e_herbrand_congr r (eM i)]
  rfl

end torEuler

end HodgeLean.Adapters

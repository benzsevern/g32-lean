import HodgeLean.RealDefs.DimensionThree
import HodgeLean.RealDefs.HodgeStructure

/-! # Cup product and the Hodge filtration

Roadmap `docs/roadmap/layer3.md` §3 O5 and C8, and the retirement of O4.

* `CupProduct.cupC`: the `ℂ`-bilinear base change of `μ.cup` to `ℂ ⊗[ℚ] HQ X i`.
* `CupFiltered` (O5): if `x` maps into `F^p` and `y` into `F^q` under `bettiDeRhamHQ`, then
  `cupC x y` maps into `F^(p+q)`. `CupFiltered.mem_conj` derives the same statement for the
  conjugate filtration from C3/U2, so it needs no field of its own.
* `CycleClassIsHodge` (C8): the span of cycle classes of codimension `p` lies in `Hdg^p(X; ℚ)`.
* `lefschetzReflectsHodge_of_cupFiltered`: O4 (`LefschetzReflectsHodge`) from O5, C2, C4, Hard
  Lefschetz and `η ∈ Hdg^1(X; ℚ)`. This is the direct route (roadmap O4, "Route A" of the brief):
  `L^r` sends the `(s, t)` piece of `H^(2p)` into the `(s + r, t + r)` piece of `H^(2m)`, so by
  uniqueness of the Hodge decomposition in degree `2m` and injectivity of `L^r`, a class whose
  image is of type `(m, m)` has no component off `(p, p)`. No Tate twist is needed.
* `hodgeConjectureInDimensionLE_three_of_cupFiltered`: the dimension `≤ 3` milestone with O5, C2,
  C4 and C8 in place of O4.

The comparison is stated through `bettiDeRhamHQ` rather than `bettiDeRham`, since `CupProduct`
lives on `HQ X n` (see `Operations`). -/

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open scoped TensorProduct

namespace HodgeLean.RealDefs

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

namespace CupProduct

/-- The `ℂ`-bilinear extension `(ℂ ⊗[ℚ] H^i) × (ℂ ⊗[ℚ] H^j) → ℂ ⊗[ℚ] H^k` of `μ.cup h`, with
`(z ⊗ a, w ⊗ b) ↦ zw ⊗ (a ∪ b)` (`cupC_tmul`). -/
noncomputable def cupC (μ : CupProduct X) {i j k : ℕ} (h : i + j = k) :
    ℂ ⊗[ℚ] HQ X i →ₗ[ℂ] ℂ ⊗[ℚ] HQ X j →ₗ[ℂ] ℂ ⊗[ℚ] HQ X k :=
  (LinearMap.baseChangeHom ℚ ℂ (HQ X j) (HQ X k) ∘ₗ μ.cup h).liftBaseChange ℂ

/-- `cupC` on pure tensors. -/
theorem cupC_tmul (μ : CupProduct X) {i j k : ℕ} (h : i + j = k) (z w : ℂ) (a : HQ X i)
    (b : HQ X j) : μ.cupC h (z ⊗ₜ a) (w ⊗ₜ b) = (z * w) ⊗ₜ μ.cup h a b := by
  rw [cupC, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.baseChangeHom_apply, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

/-- Cup product with `1 ⊗ a` is the base change of cup product with `a`. -/
theorem cupC_one_tmul (μ : CupProduct X) {i j k : ℕ} (h : i + j = k) (a : HQ X i) :
    μ.cupC h (1 ⊗ₜ a) = (μ.cup h a).baseChange ℂ := by
  rw [cupC, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

/-- `cupC` commutes with rational conjugation `sigmaQ`: it is a base change, so conjugation of the
`ℂ` factor passes through it. -/
theorem sigmaQ_cupC (μ : CupProduct X) {i j k : ℕ} (h : i + j = k) (x : ℂ ⊗[ℚ] HQ X i)
    (y : ℂ ⊗[ℚ] HQ X j) :
    HodgeBlocks.sigmaQ (HQ X k) (μ.cupC h x y) =
      μ.cupC h (HodgeBlocks.sigmaQ (HQ X i) x) (HodgeBlocks.sigmaQ (HQ X j) y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul z a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul w b =>
      change HodgeBlocks.sigmaQR _ _ =
        μ.cupC h (HodgeBlocks.sigmaQR _ (z ⊗ₜ a)) (HodgeBlocks.sigmaQR _ (w ⊗ₜ b))
      rw [cupC_tmul, HodgeBlocks.sigmaQ_tmul, HodgeBlocks.sigmaQ_tmul, HodgeBlocks.sigmaQ_tmul,
        cupC_tmul, map_mul]

end CupProduct

variable (X) in
/-- The cup product respects the Hodge filtration: for `x ∈ ℂ ⊗[ℚ] H^i` and `y ∈ ℂ ⊗[ℚ] H^j`
whose de Rham images lie in `F^p` and `F^q`, the de Rham image of `x ∪ y` lies in `F^(p+q)`.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76, §5.3 (the cup product on de Rham cohomology is induced by the wedge product of forms), Ch. 7 §7.1 (the Hodge filtration on de Rham cohomology, with filtered representatives; the wedge product of forms maps `F^p ⊗ F^q` into `F^(p+q)`) and Ch. 8 (the Hodge filtration as the image of the truncation `σ_{≥p} Ω•`), sections only.

Under the de Rham theorem the cup product on `H^*(X(ℂ); ℂ)` is induced by the wedge product of
closed forms, and the wedge product maps `F^p A^• ⊗ F^q A^•` into `F^(p+q) A^•` because it adds
holomorphic degrees. The structure takes two facts as given: that `μ.cup` agrees with the cup
product transported from forms (upstream has no product on `H_dR`), and that upstream's `F^p`
(the image of `σ_{≥p} Ω•`) is the Hodge filtration of forms. No theorem numbers are pinned.

**Conjugation.** No field is needed for the conjugate filtration `conj F^p`: `cupC` is a base
change, so it commutes with the rational conjugation `sigmaQ` (`CupProduct.sigmaQ_cupC`), and
`bettiDeRhamHQ` intertwines `sigmaQ` with `deRhamConj` (C3/U2, `bettiDeRhamHQ_sigmaQ`). Together
they give `CupFiltered.mem_conj` and `CupFiltered.mem_hodgePiece`.

**Consistency.** For `X = Spec ℂ`, `H^i = 0` for `i > 0`, so only `i = j = 0` has content. There
`H_dR^0 = ℂ`, `F^p H_dR^0` is everything for `p ≤ 0` and `0` for `p > 0`
(`hodgeFiltration_eq_top_of_nonpos`, `hodgeFiltration_eq_bot_of_lt`), and the product of two
classes, one of them `0` whenever `p > 0` or `q > 0`, lies in `F^(p+q)` in every case. This
assumes `Spec ℂ` carries a `CupProduct` (product of `ℚ` in degree `0`), which is not constructed
here.

The statement review of run `hlean-o5` (handoff batch 8) also checked `mem` at every quantified
index on three varieties, with the classical cup product (wedge product of forms), and found no
counterexample:
* `ℙ¹`: `H^0 = ℚ` of type `(0, 0)` and `H^2 = ℚ` of type `(1, 1)`; the only non-zero products
  are by the unit, which lies in `F^0`, so `F^p ∪ F^q ⊆ F^(p+q)` holds.
* An elliptic curve `E`: `H^1 = H^{1,0} ⊕ H^{0,1}` with `F^1 H^1 = H^{1,0}`, and `H^2` of type
  `(1, 1)`; the product of two `(1, 0)` classes is a `(2, 0)` class, hence `0 ∈ F^2 H^2`.
* `E × E`: `H^1` has Hodge numbers `2, 2` and `H^2` has `1, 4, 1`; the product of an `(s, t)` and
  an `(s', t')` class has type `(s + s', t + t')`, so it lies in `F^(p+q)` whenever its factors lie
  in `F^p` and `F^q`.
These are checks of the statement, not theorems here. -/
@[hodge_hypothesis]
structure CupFiltered (μ : CupProduct X) : Prop where
  mem : ∀ {i j k : ℕ} (h : i + j = k) (p q : ℤ) (x : ℂ ⊗[ℚ] HQ X i) (y : ℂ ⊗[ℚ] HQ X j),
      bettiDeRhamHQ X i x ∈ F^p H_dR^(i : ℤ)(X) → bettiDeRhamHQ X j y ∈ F^q H_dR^(j : ℤ)(X) →
      bettiDeRhamHQ X k (μ.cupC h x y) ∈ F^(p + q) H_dR^(k : ℤ)(X)

namespace CupFiltered

variable {μ : CupProduct X}

omit [IsProjective X.hom] in
/-- `bettiDeRhamHQ x` lies in the conjugate filtration `conj F^p` exactly when the de Rham image
of `sigmaQ x` lies in `F^p`. -/
theorem mem_conj_iff (n : ℕ) (p : ℤ) (x : ℂ ⊗[ℚ] HQ X n) :
    bettiDeRhamHQ X n x ∈ conjHodgeFiltrationComplexSubmodule X p n ↔
      bettiDeRhamHQ X n (HodgeBlocks.sigmaQ (HQ X n) x) ∈ F^p H_dR^(n : ℤ)(X) := by
  rw [mem_conjHodgeFiltrationComplexSubmodule, bettiDeRhamHQ_sigmaQ]

/-- The conjugate filtration is multiplicative too, with no further hypothesis: `cupC` is a base
change, so it commutes with conjugation (C3/U2). -/
theorem mem_conj (hC : CupFiltered X μ) {i j k : ℕ} (h : i + j = k) (p q : ℤ)
    (x : ℂ ⊗[ℚ] HQ X i) (y : ℂ ⊗[ℚ] HQ X j)
    (hx : bettiDeRhamHQ X i x ∈ conjHodgeFiltrationComplexSubmodule X p i)
    (hy : bettiDeRhamHQ X j y ∈ conjHodgeFiltrationComplexSubmodule X q j) :
    bettiDeRhamHQ X k (μ.cupC h x y) ∈ conjHodgeFiltrationComplexSubmodule X (p + q) k := by
  rw [mem_conj_iff] at hx hy ⊢
  rw [CupProduct.sigmaQ_cupC]
  exact hC.mem h p q _ _ hx hy

/-- The cup product sends the `(s, t)` and `(s', t')` pieces into the `(s + s', t + t')` piece. -/
theorem mem_hodgePiece (hC : CupFiltered X μ) {i j k : ℕ} (h : i + j = k) {s t s' t' : ℤ}
    (x : ℂ ⊗[ℚ] HQ X i) (y : ℂ ⊗[ℚ] HQ X j)
    (hx : bettiDeRhamHQ X i x ∈ hodgePiece X s t i)
    (hy : bettiDeRhamHQ X j y ∈ hodgePiece X s' t' j) :
    bettiDeRhamHQ X k (μ.cupC h x y) ∈ hodgePiece X (s + s') (t + t') k :=
  ⟨hC.mem h s s' x y hx.1 hy.1, hC.mem_conj h t t' x y hx.2 hy.2⟩

end CupFiltered

variable (X) in
/-- Cycle classes are Hodge classes: the span of the classes of codimension-`p` subvarieties lies
in `Hdg^p(X; ℚ)`.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76, §§11.1.2–11.1.3 (the cycle class of an analytic subvariety, and that it is a Hodge class), sections only.

Voisin constructs the class of a codimension-`p` analytic subvariety `Z` in §11.1.2, through
relative cohomology and a Thom class over the smooth locus of `Z`, then identifies it with
integration over `Z` and deduces that it is of type `(p, p)`: a `(s, t)`-form with
`s + t = 2 dim Z` restricts to zero on `Z` unless `s = t = dim Z`. Upstream's
`cycleComponentSheafClass` is defined through local cohomology with supports; the structure takes
the agreement of upstream's class with Voisin's as part of the hypothesis.

**Consistency.** For `p = 0` the only codimension-`0` cycle is `X` itself, whose class is the unit
(`cycleComponentSheafClass_generic`), and the unit is a Hodge class (`F^0 = ⊤`). For `X = ℙ¹` and
`p = 1`, the class of a point spans `H^2(ℙ¹; ℚ)`, which is of type `(1, 1)`. Neither is proved here
for upstream's `Hdg^p`. -/
@[hodge_hypothesis]
structure CycleClassIsHodge : Prop where
  le : ∀ p : ℕ, algebraicCycleClassSpan X p ≤ Hdg^p(X; ℚ)

/-- Linear algebra behind the reflection: let `f : M → N` be injective and send each piece `A i`
of a spanning family into the piece `B (g i)` of an independent family, with `g` injective. If
`f x ∈ B (g i₀)`, then `x ∈ A i₀`. -/
theorem mem_of_map_mem_of_iSupIndep_of_map_le {R M N ι κ : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {A : ι → Submodule R M} {B : κ → Submodule R N}
    (hA : iSup A = ⊤) (hB : iSupIndep B) {g : ι → κ} (hg : Function.Injective g)
    {f : M →ₗ[R] N} (hf : Function.Injective f) (hfA : ∀ i, (A i).map f ≤ B (g i))
    {i₀ : ι} {x : M} (hx : f x ∈ B (g i₀)) : x ∈ A i₀ := by
  have hx' : x ∈ A i₀ ⊔ ⨆ (i) (_ : i ≠ i₀), A i := by
    rw [← iSup_split_single, hA]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
  have hfy : f y ∈ B (g i₀) := hfA i₀ (Submodule.mem_map_of_mem hy)
  have hz₁ : f z ∈ B (g i₀) := by
    have := (B (g i₀)).sub_mem hx hfy
    rwa [map_add, add_sub_cancel_left] at this
  have hz₂ : f z ∈ ⨆ (j) (_ : j ≠ g i₀), B j := by
    refine (Submodule.map_le_iff_le_comap.mpr (iSup₂_le fun i hi => ?_))
      (Submodule.mem_map_of_mem hz)
    exact Submodule.map_le_iff_le_comap.mp
      ((hfA i).trans (le_iSup₂_of_le (g i) (hg.ne hi) le_rfl))
  have h0 : f z = 0 := (Submodule.disjoint_def.mp (hB (g i₀))) _ hz₁ hz₂
  rw [← map_zero f] at h0
  rw [hf h0, add_zero]
  exact hy

@[deprecated (since := "2026-10-20")]
alias mem_of_map_mem_of_iSupIndep := mem_of_map_mem_of_iSupIndep_of_map_le

omit [IsProjective X.hom] in
/-- `a ∈ Hdg^p(X; ℚ)` exactly when `1 ⊗ a` lies in the `(p, p)` piece `cohomologyHodgePiece`. -/
theorem mem_hodgeClasses_iff_tmul_mem (p : ℕ) (a : HQ X (2 * p)) :
    (a : H^(2 * p)(X; ℚ)) ∈ Hdg^p(X; ℚ) ↔
      (1 : ℂ) ⊗ₜ[ℚ] a ∈ cohomologyHodgePiece X (2 * p) ((p : ℤ), (p : ℤ)) := by
  have h : ((p : ℤ), (p : ℤ)).1 + ((p : ℤ), (p : ℤ)).2 = ((2 * p : ℕ) : ℤ) := by push_cast; ring
  rw [cohomologyHodgePiece, ite_eq_left_of_eq_true _ _ (eq_true h), Submodule.mem_comap,
    bettiDeRhamHQ_tmul, one_smul]
  rfl

/-- One step of the Lefschetz power, as linear maps. -/
theorem lefschetzPow_succ_eq (μ : CupProduct X) (η : HQ X 2) (r : ℕ) {k m' m : ℕ}
    (h : k + 2 * (r + 1) = m) (h' : k + 2 * r = m') (h'' : 2 + m' = m) :
    lefschetzPow X μ η (r + 1) h = μ.cup h'' η ∘ₗ lefschetzPow X μ η r h' :=
  LinearMap.ext (lefschetzPow_succ μ η r h h' h'')

/-- With `η` of type `(1, 1)`, the complexified Lefschetz power `L^r` sends the `(s, t)` piece
into the `(s + r, t + r)` piece. -/
theorem baseChange_lefschetzPow_mem_hodgePiece {μ : CupProduct X} {η : HQ X 2}
    (hC : CupFiltered X μ) (hη : bettiDeRhamHQ X 2 (1 ⊗ₜ η) ∈ hodgePiece X 1 1 2) :
    ∀ (r : ℕ) {k m : ℕ} (h : k + 2 * r = m) (s t : ℤ) (x : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X k x ∈ hodgePiece X s t k →
      bettiDeRhamHQ X m ((lefschetzPow X μ η r h).baseChange ℂ x) ∈
        hodgePiece X (s + r) (t + r) m
  | 0, k, m, h, s, t, x, hx => by
    obtain rfl : m = k := by omega
    rw [show lefschetzPow X μ η 0 h = LinearMap.id from LinearMap.ext (lefschetzPow_zero μ η h),
      LinearMap.baseChange_id]
    simpa using hx
  | r + 1, k, m, h, s, t, x, hx => by
    have h' : k + 2 * r = k + 2 * r := rfl
    have h'' : 2 + (k + 2 * r) = m := by omega
    rw [lefschetzPow_succ_eq μ η r h h' h'', LinearMap.baseChange_comp, LinearMap.comp_apply,
      ← CupProduct.cupC_one_tmul]
    have := hC.mem_hodgePiece h'' (1 ⊗ₜ η) _ hη
      (baseChange_lefschetzPow_mem_hodgePiece hC hη r h' s t x hx)
    convert this using 2 <;> push_cast <;> ring

/-- **Reflection of Hodge classes (O4) from O5.** Under the Betti–de Rham comparison (C2), the
Hodge decomposition (C4), Hard Lefschetz and the cup product respecting the Hodge filtration (O5),
with `η` a Hodge class of degree two, `L^r a` Hodge with `2p + r = dim X` forces `a` Hodge.

The proof is the direct route: `L^r` maps the `(s, t)` piece of `H^(2p)` into the `(s + r, t + r)`
piece of `H^(2m)` (`baseChange_lefschetzPow_mem_hodgePiece`), the pieces of `H^(2m)` are
independent (C4), and `L^r` is injective (Hard Lefschetz, then base change to `ℂ`), so
`mem_of_map_mem_of_iSupIndep_of_map_le` puts `1 ⊗ a` in the `(p, p)` piece.

The argument list is the brief's less `FiniteBetti X`: the proof never uses finite-dimensionality,
since it works with the pieces `cohomologyHodgePiece` directly rather than with the Blocks
structure `cohomologyHodgeStructure`, so the hypothesis is dropped.

Checks: F-1686 -/
theorem lefschetzReflectsHodge_of_cupFiltered {μ : CupProduct X} {η : HQ X 2}
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hC : CupFiltered X μ)
    (hL : HardLefschetz X μ η) (hη : (η : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ)) :
    LefschetzReflectsHodge X μ η := by
  refine ⟨fun {p r m} h hr a hb => ?_⟩
  have hη' : bettiDeRhamHQ X 2 (1 ⊗ₜ η) ∈ hodgePiece X 1 1 2 := by
    have := (mem_hodgeClasses_iff_tmul_mem 1 η).mp hη
    simpa [cohomologyHodgePiece] using this
  rw [mem_hodgeClasses_iff_tmul_mem] at hb ⊢
  have hint : ∀ n, DirectSum.IsInternal (cohomologyHodgePiece X n) := fun n => by
    rw [cohomologyHodgePiece_eq_map hB n]
    exact (hD.isInternal n).mapEquiv _
  have hinj : Function.Injective (lefschetzPow X μ η r h) := by
    have hk : 2 * p ≤ dim X.left := by omega
    have hr' : r = dim X.left - 2 * p := by omega
    subst hr'
    exact (hL.bijective hk h).1
  have hinjC : Function.Injective ((lefschetzPow X μ η r h).baseChange ℂ) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  refine mem_of_map_mem_of_iSupIndep_of_map_le (hint (2 * p)).submodule_iSup_eq_top
    (hint (2 * m)).submodule_iSupIndep (g := fun st : ℤ × ℤ => (st.1 + r, st.2 + r))
    (fun a b hab => ?_) hinjC (fun st => ?_) (x := (1 : ℂ) ⊗ₜ[ℚ] a) ?_
  · simp only [Prod.mk.injEq, add_left_inj] at hab
    exact Prod.ext hab.1 hab.2
  · rintro _ ⟨x, hx, rfl⟩
    unfold cohomologyHodgePiece at hx ⊢
    by_cases hst : st.1 + st.2 = ((2 * p : ℕ) : ℤ)
    · have hst' : st.1 + r + (st.2 + r) = ((2 * m : ℕ) : ℤ) := by push_cast at hst ⊢; omega
      simp only [hst, hst', ↓reduceIte] at hx ⊢
      exact baseChange_lefschetzPow_mem_hodgePiece hC hη' r h st.1 st.2 x hx
    · simp only [hst, ↓reduceIte] at hx
      rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
      exact Submodule.zero_mem _
  · rw [LinearMap.baseChange_tmul]
    convert hb using 3 <;> push_cast <;> omega

/-- **The Hodge conjecture in dimension at most three**, upstream's `HodgeConjectureInDimensionLE 3`,
with the bundled reflection hypothesis `LefschetzReflectsHodge` (O4) replaced by more primitive
ones: the Betti–de Rham comparison (C2), the Hodge decomposition (C4) and cycle classes being Hodge
(C8) for every `X`, and, for `X` of dimension at most three, a cup product `μ` respecting the Hodge
filtration (O5) with a class `η` satisfying Hard Lefschetz and divisor closure. Reflection is
derived by `lefschetzReflectsHodge_of_cupFiltered`, using that `η`, a divisor class
(`AlgebraicTimesDivisor.η_mem`), is a Hodge class by C8.

Source: Lewis, *A Survey of the Hodge Conjecture*, 2nd ed., CRM Monograph Ser. 10, the argument that Lefschetz (1,1) and hard Lefschetz give the conjecture in dimension at most three, section-level; proof shape from `docs/roadmap/layer3.md` §2(a), with O4 derived as in §3 O4.

The brief's hypothesis list also had `FiniteBetti` for every `X`; the derivation never uses it, so
it is omitted, which only strengthens the theorem.

**U3 (closed, `docs/notes/fundamental-class-unit.md`).** `CupProduct X` requires the class of
`X` (upstream's `cycleComponentSheafClass` of the generic point) to equal the unit `unitClass X`
(`CupProduct.fundamentalClass_eq_unit`). That holds for every eligible `X`
(`cycleComponentSheafClass_generic`, in `FundamentalClassUnit.lean`), so `hops` is not vacuous on
this account. No `CupProduct` instance is constructed here, so whether `hops` holds for a given `X`
still rests on the cup product's other fields (unit, associativity, graded commutativity), which
hold classically.

Checks: F-1687 -/
@[hodge_milestone] theorem hodgeConjectureInDimensionLE_three_of_cupFiltered
    (h11 : LefschetzOneOneHyp) (hconn : ComplexPointsPreconnected)
    (hops : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      dim X.left ≤ 3 → ∃ (μ : CupProduct X) (η : HQ X 2),
        HardLefschetz X μ η ∧ AlgebraicTimesDivisor X μ η ∧ CupFiltered X μ)
    (hvan : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      VanishingAboveTop X)
    (hB : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      BettiDeRhamIso X)
    (hD : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HodgeDecomposition X)
    (hcyc : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      CycleClassIsHodge X) :
    HodgeConjectureInDimensionLE 3 := by
  refine hodgeConjectureInDimensionLE_three h11 hconn (fun X _ _ _ hX => ?_) hvan
  obtain ⟨μ, η, hL, hA, hC⟩ := hops X hX
  exact ⟨μ, η, hL, hA, lefschetzReflectsHodge_of_cupFiltered (hB X) (hD X) hC hL
    ((hcyc X).le 1 hA.η_mem)⟩

end HodgeLean.RealDefs

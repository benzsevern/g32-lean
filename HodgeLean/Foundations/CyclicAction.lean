import Mathlib

/-!
# Finite-order automorphisms: the cyclotomic isotypic decomposition

Let `V` be a `ℚ`-vector space and `σ : V →ₗ[ℚ] V` with `σ ^ m = 1`, `0 < m`. The decomposition
and the imaginary quadratic actions hold for any `V`; only the eigenspace decomposition over `ℂ`
assumes `V` finite-dimensional.
Since `X ^ m - 1 = ∏_{d ∣ m} Φ_d` with the `Φ_d` pairwise coprime over `ℚ`, the space splits as
`V = ⨁_{d ∣ m} ker Φ_d(σ)`.  This file proves that decomposition, the imaginary quadratic action
on the `Φ₃`, `Φ₄` and `Φ₆` parts, the eigenspace decomposition over `ℂ`, and the preservation of
`σ`-stable complex subspaces by every polynomial in `σ`.

HC: no distance.  AV milestone: no distance.  F-953's Weil space and the cyclic-cover `K`-action
become statable.
-/

open Polynomial Function

noncomputable section

namespace HodgeLean.Foundations

section General

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `p ∣ q`, then `ker p(f) ≤ ker q(f)`. -/
theorem ker_aeval_le_ker_aeval_of_dvd (f : Module.End R M) {p q : R[X]} (h : p ∣ q) :
    LinearMap.ker (aeval f p) ≤ LinearMap.ker (aeval f q) := by
  obtain ⟨r, rfl⟩ := h
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [mul_comm, aeval_mul, Module.End.mul_apply, hv, map_zero]

/-- For a finite family of pairwise coprime polynomials, the kernels add up to the kernel of the
product. -/
theorem iSup_ker_aeval_eq_ker_aeval_prod {ι : Type*} [DecidableEq ι] (f : Module.End R M)
    (s : Finset ι) (p : ι → R[X]) (hp : (s : Set ι).Pairwise (IsCoprime on p)) :
    ⨆ i ∈ s, LinearMap.ker (aeval f (p i)) = LinearMap.ker (aeval f (∏ i ∈ s, p i)) := by
  induction s using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert a t ha ih =>
    have ht : (t : Set ι).Pairwise (IsCoprime on p) :=
      hp.mono (by simp [Set.subset_insert])
    have hcop : IsCoprime (p a) (∏ i ∈ t, p i) := by
      refine IsCoprime.prod_right fun i hi => hp (by simp) (by simp [hi]) ?_
      rintro rfl
      exact ha hi
    rw [Finset.iSup_insert, ih ht, Finset.prod_insert ha,
      sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop]

/-- For a finite family of pairwise coprime polynomials whose product kills `f`, the kernels form
an internal direct sum decomposition of `M`. -/
theorem isInternal_ker_aeval {ι : Type*} [DecidableEq ι] (f : Module.End R M)
    (s : Finset ι) (p : ι → R[X]) (hp : (s : Set ι).Pairwise (IsCoprime on p))
    (hf : aeval f (∏ i ∈ s, p i) = 0) :
    DirectSum.IsInternal (fun i : s => LinearMap.ker (aeval f (p i))) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    have hle : ⨆ (j : s) (_ : j ≠ i), LinearMap.ker (aeval f (p j)) ≤
        LinearMap.ker (aeval f (∏ k ∈ s.erase i, p k)) := by
      refine iSup₂_le fun j hj => ker_aeval_le_ker_aeval_of_dvd f ?_
      refine Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨?_, j.2⟩)
      exact fun h => hj (Subtype.ext h)
    refine Disjoint.mono_right hle (disjoint_ker_aeval_of_isCoprime f ?_)
    refine IsCoprime.prod_right fun k hk => hp i.2 (Finset.mem_of_mem_erase hk) ?_
    exact (Finset.ne_of_mem_erase hk).symm
  · have h : ⨆ i ∈ s, LinearMap.ker (aeval f (p i)) = ⨆ i : s, LinearMap.ker (aeval f (p i)) :=
      iSup_subtype'
    rw [← h, iSup_ker_aeval_eq_ker_aeval_prod f s p hp, hf, LinearMap.ker_zero]

end General

section Isotypic

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The `Φ_d`-isotypic part `ker Φ_d(σ)` of a `ℚ`-linear endomorphism `σ`, where `Φ_d` is the
`d`-th cyclotomic polynomial.

When `σ ^ m = 1`, the space is the direct sum of the `isotypic σ d` for `d ∣ m`
(`isInternal_isotypic`).  Warning on names: `isotypic σ m` (the `Φ_m` part) is the **primitive**
part, the space F-953 calls `P`, on which `σ` has no eigenvalue of order less than `m` over `ℂ`;
`isotypic σ d` for a proper divisor `d < m` is *not* the primitive part.

HC: no distance.  AV milestone: no distance.  F-953's Weil space and the cyclic-cover `K`-action
become statable.

Source: S. Lang, *Algebra* (rev. 3rd ed., Springer GTM 211), the decomposition of a module over
`k[X]` into primary parts by the coprime factors of an annihilating polynomial. -/
def isotypic (σ : V →ₗ[ℚ] V) (d : ℕ) : Submodule ℚ V :=
  LinearMap.ker (aeval σ (cyclotomic d ℚ))

theorem mem_isotypic {σ : V →ₗ[ℚ] V} {d : ℕ} {v : V} :
    v ∈ isotypic σ d ↔ aeval σ (cyclotomic d ℚ) v = 0 :=
  LinearMap.mem_ker

theorem isotypic_eq_top_iff {σ : V →ₗ[ℚ] V} {d : ℕ} :
    isotypic σ d = ⊤ ↔ aeval σ (cyclotomic d ℚ) = 0 :=
  LinearMap.ker_eq_top

/-- Every polynomial in `σ` maps `isotypic σ d` into itself. -/
theorem aeval_mem_isotypic (σ : V →ₗ[ℚ] V) (d : ℕ) (p : ℚ[X]) {v : V}
    (hv : v ∈ isotypic σ d) : aeval σ p v ∈ isotypic σ d := by
  rw [mem_isotypic] at hv ⊢
  rw [← Module.End.mul_apply, ← aeval_mul, mul_comm, aeval_mul, Module.End.mul_apply, hv,
    map_zero]

/-- `isotypic σ d` is `σ`-invariant. -/
theorem map_mem_isotypic (σ : V →ₗ[ℚ] V) (d : ℕ) {v : V} (hv : v ∈ isotypic σ d) :
    σ v ∈ isotypic σ d := by
  simpa using aeval_mem_isotypic σ d X hv

/-- `isotypic σ d` is invariant under `2σ + 1`. -/
theorem two_smul_add_one_mem_isotypic (σ : V →ₗ[ℚ] V) (d : ℕ) :
    ∀ v ∈ isotypic σ d, ((2 : ℚ) • σ + 1) v ∈ isotypic σ d := fun v hv => by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  exact add_mem (Submodule.smul_mem _ _ (map_mem_isotypic σ d hv)) hv

/-- `isotypic σ d` is invariant under `2σ - 1`. -/
theorem two_smul_sub_one_mem_isotypic (σ : V →ₗ[ℚ] V) (d : ℕ) :
    ∀ v ∈ isotypic σ d, ((2 : ℚ) • σ - 1) v ∈ isotypic σ d := fun v hv => by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  exact sub_mem (Submodule.smul_mem _ _ (map_mem_isotypic σ d hv)) hv

/-- **The cyclotomic isotypic decomposition.**  If `σ ^ m = 1` with `0 < m`, then `V` is the
internal direct sum of the `Φ_d`-isotypic parts `ker Φ_d(σ)`, `d ∣ m`.  The `Φ_m` part is the
primitive part (F-953's `P`). -/
theorem isInternal_isotypic (σ : V →ₗ[ℚ] V) {m : ℕ} (hm : 0 < m) (hσ : σ ^ m = 1) :
    DirectSum.IsInternal (fun d : m.divisors => isotypic σ d) :=
  isInternal_ker_aeval σ m.divisors (fun d => cyclotomic d ℚ)
    (fun _ _ _ _ hab => cyclotomic.isCoprime_rat hab)
    (by rw [prod_cyclotomic_eq_X_pow_sub_one hm, map_sub, map_pow, aeval_X, map_one, hσ,
      sub_self])

end Isotypic

section ImaginaryQuadratic

/-! ### The imaginary quadratic action on the `Φ₃`, `Φ₄` and `Φ₆` parts

On `ker Φ₃(σ)` (`Φ₃ = X² + X + 1`), `J := 2σ + 1` satisfies `J² = 4Φ₃(σ) - 3 = -3`; on
`ker Φ₆(σ)` (`Φ₆ = X² - X + 1`), `J := 2σ - 1` satisfies `J² = 4Φ₆(σ) - 3 = -3`; on
`ker Φ₄(σ)` (`Φ₄ = X² + 1`), `J := σ` satisfies `J² = -1`.  So these parts carry actions of
`ℚ(√-3)` and `ℚ(i)`.  Note that the `Φ₆` formula on a `Φ₃` part is wrong (see the examples). -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem cyclotomic_four_rat : cyclotomic 4 ℚ = X ^ 2 + 1 := by
  rw [show (4 : ℕ) = 2 ^ (1 + 1) by norm_num,
    cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [Finset.sum_range_succ, add_comm]

theorem two_smul_add_one_apply_apply_of_mem_isotypic_three (σ : V →ₗ[ℚ] V) {v : V}
    (hv : v ∈ isotypic σ 3) :
    ((2 : ℚ) • σ + 1) (((2 : ℚ) • σ + 1) v) = (-3 : ℚ) • v := by
  rw [mem_isotypic, cyclotomic_three] at hv
  simp only [map_add, map_mul, aeval_X, map_one, LinearMap.add_apply, pow_two,
    Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply, map_smul] at hv ⊢
  linear_combination (norm := module) (4 : ℚ) • hv

theorem two_smul_sub_one_apply_apply_of_mem_isotypic_six (σ : V →ₗ[ℚ] V) {v : V}
    (hv : v ∈ isotypic σ 6) :
    ((2 : ℚ) • σ - 1) (((2 : ℚ) • σ - 1) v) = (-3 : ℚ) • v := by
  rw [mem_isotypic, cyclotomic_six] at hv
  simp only [map_add, map_sub, map_mul, aeval_X, map_one, LinearMap.add_apply,
    LinearMap.sub_apply, pow_two, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.smul_apply, map_smul] at hv ⊢
  linear_combination (norm := module) (4 : ℚ) • hv

theorem apply_apply_of_mem_isotypic_four (σ : V →ₗ[ℚ] V) {v : V} (hv : v ∈ isotypic σ 4) :
    σ (σ v) = (-1 : ℚ) • v := by
  rw [mem_isotypic, cyclotomic_four_rat] at hv
  simp only [map_add, map_mul, aeval_X, map_one, LinearMap.add_apply, pow_two,
    Module.End.mul_apply, Module.End.one_apply] at hv
  linear_combination (norm := module) hv

/-- On the `Φ₃` part, `J := 2σ + 1` satisfies `J ∘ J = -3`: an action of `ℚ(√-3)`. -/
theorem restrict_two_smul_add_one_comp_self_isotypic_three (σ : V →ₗ[ℚ] V) :
    (((2 : ℚ) • σ + 1).restrict (two_smul_add_one_mem_isotypic σ 3)).comp
        (((2 : ℚ) • σ + 1).restrict (two_smul_add_one_mem_isotypic σ 3)) =
      (-3 : ℚ) • LinearMap.id := by
  ext ⟨v, hv⟩
  exact two_smul_add_one_apply_apply_of_mem_isotypic_three σ hv

/-- On the `Φ₆` part, `J := 2σ - 1` satisfies `J ∘ J = -3`: an action of `ℚ(√-3)`. -/
theorem restrict_two_smul_sub_one_comp_self_isotypic_six (σ : V →ₗ[ℚ] V) :
    (((2 : ℚ) • σ - 1).restrict (two_smul_sub_one_mem_isotypic σ 6)).comp
        (((2 : ℚ) • σ - 1).restrict (two_smul_sub_one_mem_isotypic σ 6)) =
      (-3 : ℚ) • LinearMap.id := by
  ext ⟨v, hv⟩
  exact two_smul_sub_one_apply_apply_of_mem_isotypic_six σ hv

/-- On the `Φ₄` part, `J := σ` satisfies `J ∘ J = -1`: an action of `ℚ(i)`. -/
theorem restrict_comp_self_isotypic_four (σ : V →ₗ[ℚ] V) :
    (σ.restrict (fun _ hv => map_mem_isotypic σ 4 hv)).comp
        (σ.restrict (fun _ hv => map_mem_isotypic σ 4 hv)) =
      (-1 : ℚ) • LinearMap.id := by
  ext ⟨v, hv⟩
  exact apply_apply_of_mem_isotypic_four σ hv

/-- If `Φ₃(σ) = 0` on all of `V`, then `(2σ + 1) ∘ (2σ + 1) = -3` on `V`. -/
theorem two_smul_add_one_comp_self_of_isotypic_three_eq_top {σ : V →ₗ[ℚ] V}
    (h : isotypic σ 3 = ⊤) :
    ((2 : ℚ) • σ + 1).comp ((2 : ℚ) • σ + 1) = (-3 : ℚ) • LinearMap.id := by
  ext v
  exact two_smul_add_one_apply_apply_of_mem_isotypic_three σ (h ▸ Submodule.mem_top)

/-- If `Φ₆(σ) = 0` on all of `V`, then `(2σ - 1) ∘ (2σ - 1) = -3` on `V`. -/
theorem two_smul_sub_one_comp_self_of_isotypic_six_eq_top {σ : V →ₗ[ℚ] V}
    (h : isotypic σ 6 = ⊤) :
    ((2 : ℚ) • σ - 1).comp ((2 : ℚ) • σ - 1) = (-3 : ℚ) • LinearMap.id := by
  ext v
  exact two_smul_sub_one_apply_apply_of_mem_isotypic_six σ (h ▸ Submodule.mem_top)

/-- If `Φ₄(σ) = 0` on all of `V`, then `σ ∘ σ = -1` on `V`. -/
theorem comp_self_of_isotypic_four_eq_top {σ : V →ₗ[ℚ] V} (h : isotypic σ 4 = ⊤) :
    σ.comp σ = (-1 : ℚ) • LinearMap.id := by
  ext v
  exact apply_apply_of_mem_isotypic_four σ (h ▸ Submodule.mem_top)

end ImaginaryQuadratic

section Complex

/-! ### Over `ℂ`: eigenspaces of the complexification -/

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Complexification commutes with evaluating a polynomial at `σ`. -/
theorem baseChange_aeval (σ : V →ₗ[ℚ] V) (p : ℚ[X]) :
    (aeval σ p).baseChange ℂ = aeval (σ.baseChange ℂ) (p.map (algebraMap ℚ ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.baseChange_add, hp, hq, Polynomial.map_add, map_add]
  | monomial n a =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def, LinearMap.baseChange_smul, LinearMap.baseChange_pow, algebraMap_smul]

/-- Over a field, complexification commutes with taking kernels (`ℂ` is flat over `ℚ`). -/
theorem ker_baseChange (f : V →ₗ[ℚ] V) :
    LinearMap.ker (f.baseChange ℂ) = (LinearMap.ker f).baseChange ℂ :=
  Module.Flat.ker_lTensor_eq ℂ ℂ f

theorem ker_aeval_X_sub_C {W : Type*} [AddCommGroup W] [Module ℂ W] (f : Module.End ℂ W)
    (μ : ℂ) : LinearMap.ker (aeval f (X - C μ)) = Module.End.eigenspace f μ := by
  rw [Module.End.eigenspace_def]
  simp [Algebra.algebraMap_eq_smul_one]

/-- The complexification of the `Φ_d`-isotypic part is the sum of the eigenspaces of
`σ.baseChange ℂ` for the primitive `d`-th roots of unity. -/
theorem baseChange_isotypic (σ : V →ₗ[ℚ] V) {d : ℕ} (hd : 0 < d) :
    (isotypic σ d).baseChange ℂ =
      ⨆ ζ ∈ primitiveRoots d ℂ, Module.End.eigenspace (σ.baseChange ℂ) ζ := by
  classical
  rw [isotypic, ← ker_baseChange, baseChange_aeval, map_cyclotomic,
    cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp d hd.ne'),
    ← iSup_ker_aeval_eq_ker_aeval_prod _ _ (fun μ : ℂ => X - C μ)
      (fun a _ b _ hab => pairwise_coprime_X_sub_C (s := id) injective_id hab)]
  simp_rw [ker_aeval_X_sub_C]

variable [FiniteDimensional ℚ V]

/-- **The eigenspace decomposition over `ℂ`.**  If `σ ^ m = 1` with `0 < m`, the complexification
`ℂ ⊗[ℚ] V` is the internal direct sum of the eigenspaces of `σ.baseChange ℂ` for the `m`-th roots
of unity, indexed by the group `rootsOfUnity m ℂ` (a subgroup of `ℂˣ`).  Eigenspaces for
non-primitive roots are included, and may be zero. -/
theorem isInternal_eigenspace_baseChange (σ : V →ₗ[ℚ] V) {m : ℕ} (hm : 0 < m)
    (hσ : σ ^ m = 1) :
    DirectSum.IsInternal (fun ζ : rootsOfUnity m ℂ =>
      Module.End.eigenspace (σ.baseChange ℂ) ((ζ : ℂˣ) : ℂ)) := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  have hσc : σ.baseChange ℂ ^ m = 1 := by
    rw [← LinearMap.baseChange_pow, hσ, Module.End.one_eq_id, LinearMap.baseChange_id]
    rfl
  have hsemi : Module.End.IsSemisimple (σ.baseChange ℂ : Module.End ℂ (ℂ ⊗[ℚ] V)) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := (X ^ m - C 1 : ℂ[X]))
      (separable_X_pow_sub_C 1 (by exact_mod_cast hm.ne') one_ne_zero).squarefree
      (by simp [hσc])
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨(Module.End.eigenspaces_iSupIndep (σ.baseChange ℂ)).comp
    (fun a b h => Subtype.ext (Units.ext h)), ?_⟩
  rw [eq_top_iff, ← hsemi.iSup_eigenspace_eq_top]
  refine iSup_le fun μ x hx => ?_
  by_cases h0 : x = 0
  · simp [h0]
  have hpow := (Module.End.hasEigenvector_iff.mpr ⟨hx, h0⟩).pow_apply m
  rw [hσc, Module.End.one_apply] at hpow
  have hμ : μ ^ m = 1 := by
    have h1 : (μ ^ m - 1) • x = 0 := by rw [sub_smul, ← hpow, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right h0)
  exact Submodule.mem_iSup_of_mem (rootsOfUnity.mkOfPowEq μ hμ)
    (by rwa [rootsOfUnity.coe_mkOfPowEq])

end Complex

section Preserved

/-! ### Subspaces preserved by `σ` are preserved by every polynomial in `σ` -/

open scoped TensorProduct

/-- A submodule stable under `f` is stable under every polynomial in `f`. -/
theorem aeval_mem_of_forall_mem {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (f : Module.End R W) {N : Submodule R W} (hN : ∀ x ∈ N, f x ∈ N) (p : R[X]) :
    ∀ x ∈ N, aeval f p x ∈ N := by
  induction p using Polynomial.induction_on with
  | C a => intro x hx; simpa [Algebra.algebraMap_eq_smul_one] using N.smul_mem a hx
  | add p q hp hq => intro x hx; simpa using N.add_mem (hp x hx) (hq x hx)
  | monomial n a ih =>
    intro x hx
    rw [pow_succ, ← mul_assoc, aeval_mul, aeval_X, Module.End.mul_apply]
    exact ih _ (hN x hx)

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- If `σ.baseChange ℂ` maps a complex subspace `N` of `ℂ ⊗[ℚ] V` into itself, so does
`(p(σ)).baseChange ℂ` for every `p : ℚ[X]`. -/
theorem map_baseChange_aeval_le (σ : V →ₗ[ℚ] V) {N : Submodule ℂ (ℂ ⊗[ℚ] V)}
    (hN : N.map (σ.baseChange ℂ) ≤ N) (p : ℚ[X]) :
    N.map ((aeval σ p).baseChange ℂ) ≤ N := by
  rw [Submodule.map_le_iff_le_comap] at hN ⊢
  intro x hx
  rw [Submodule.mem_comap, baseChange_aeval]
  exact aeval_mem_of_forall_mem (N := N) _ (fun y hy => hN hy) _ x hx

/-- **Pieces preserved.**  If `σ.baseChange ℂ` maps each member of a family `H` of complex
subspaces of `ℂ ⊗[ℚ] V` (for instance the Hodge pieces) into itself, so does the
complexification of every polynomial in `σ`: in particular every isotypic projector
(`exists_isotypic_projector`) and every `J` of the imaginary quadratic section. -/
theorem map_baseChange_aeval_le_of_forall {ι : Type*} (σ : V →ₗ[ℚ] V)
    (H : ι → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : ∀ i, (H i).map (σ.baseChange ℂ) ≤ H i)
    (p : ℚ[X]) (i : ι) : (H i).map ((aeval σ p).baseChange ℂ) ≤ H i :=
  map_baseChange_aeval_le σ (hH i) p

/-- The `J := 2σ + 1` of the `Φ₃` part preserves every `σ`-stable complex subspace. -/
theorem map_baseChange_two_smul_add_one_le (σ : V →ₗ[ℚ] V) {N : Submodule ℂ (ℂ ⊗[ℚ] V)}
    (hN : N.map (σ.baseChange ℂ) ≤ N) :
    N.map (((2 : ℚ) • σ + 1).baseChange ℂ) ≤ N := by
  have h : aeval σ (C (2 : ℚ) * X + 1) = (2 : ℚ) • σ + 1 := by
    rw [map_add, map_mul, aeval_C, aeval_X, map_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
  rw [← h]
  exact map_baseChange_aeval_le σ hN _

/-- The `J := 2σ - 1` of the `Φ₆` part preserves every `σ`-stable complex subspace. -/
theorem map_baseChange_two_smul_sub_one_le (σ : V →ₗ[ℚ] V) {N : Submodule ℂ (ℂ ⊗[ℚ] V)}
    (hN : N.map (σ.baseChange ℂ) ≤ N) :
    N.map (((2 : ℚ) • σ - 1).baseChange ℂ) ≤ N := by
  have h : aeval σ (C (2 : ℚ) * X - 1) = (2 : ℚ) • σ - 1 := by
    rw [map_sub, map_mul, aeval_C, aeval_X, map_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
  rw [← h]
  exact map_baseChange_aeval_le σ hN _

/-- **Isotypic projectors are polynomials in `σ`.**  For `d ∣ m`, there is `e : ℚ[X]` such that
`e(σ)` is the identity on `isotypic σ d` and zero on `isotypic σ d'` for every other `d' ∣ m`.
So, when `σ ^ m = 1`, `e(σ)` is the projector of `isInternal_isotypic` onto the `Φ_d` part, and
`map_baseChange_aeval_le_of_forall` applies to it. -/
theorem exists_isotypic_projector (σ : V →ₗ[ℚ] V) (m d : ℕ) :
    ∃ e : ℚ[X], (∀ v ∈ isotypic σ d, aeval σ e v = v) ∧
      ∀ d' ∈ m.divisors, d' ≠ d → ∀ v ∈ isotypic σ d', aeval σ e v = 0 := by
  classical
  have hcop : IsCoprime (cyclotomic d ℚ) (∏ k ∈ m.divisors.erase d, cyclotomic k ℚ) :=
    IsCoprime.prod_right fun k hk => cyclotomic.isCoprime_rat (Finset.ne_of_mem_erase hk).symm
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨b * ∏ k ∈ m.divisors.erase d, cyclotomic k ℚ, fun v hv => ?_, fun d' hd' hne v hv => ?_⟩
  · have h := congr(aeval σ $hab v)
    rw [map_add, map_one, LinearMap.add_apply, aeval_mul, Module.End.mul_apply,
      mem_isotypic.mp hv, map_zero, zero_add, Module.End.one_apply] at h
    exact h
  · have hle := ker_aeval_le_ker_aeval_of_dvd σ
      (Finset.dvd_prod_of_mem (fun k => cyclotomic k ℚ) (Finset.mem_erase.mpr ⟨hne, hd'⟩))
    rw [aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.mp (hle hv), map_zero]

end Preserved

section Examples

/-! ### Examples

`ρ₃` is the rotation by `2π/3` on `ℚ²`, `-ρ₃` has order 6, `ρ₄` is the rotation by `π/2`, and
`π₃` is the cyclic permutation of the coordinates of `ℚ³`. -/

local notation "ρ₃" => Matrix.toLin' !![(0 : ℚ), -1; 1, -1]
local notation "ρ₄" => Matrix.toLin' !![(0 : ℚ), -1; 1, 0]
local notation "π₃" => Matrix.toLin' !![(0 : ℚ), 0, 1; 1, 0, 0; 0, 1, 0]

/-- The rotation `ρ₃` has order dividing 3. -/
example : ρ₃ ^ 3 = 1 := by
  apply LinearMap.toMatrix'.injective
  simp [pow_succ, LinearMap.toMatrix'_mul, Matrix.one_fin_two]

/-- All of `ℚ²` is the `Φ₃` part of `ρ₃`. -/
example : isotypic ρ₃ 3 = ⊤ := by
  rw [isotypic_eq_top_iff]
  apply LinearMap.toMatrix'.injective
  simp [cyclotomic_three, pow_two, LinearMap.toMatrix'_mul, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- The `Φ₁` part of `ρ₃` (its fixed vectors) is zero. -/
example : isotypic ρ₃ 1 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [mem_isotypic, cyclotomic_one] at hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Submodule.mem_bot]
  ext i; fin_cases i <;> simp <;> linarith

/-- `J := 2ρ₃ + 1` squares to `-3` on `ℚ²`. -/
example : ((2 : ℚ) • ρ₃ + 1).comp ((2 : ℚ) • ρ₃ + 1) = (-3 : ℚ) • LinearMap.id := by
  refine two_smul_add_one_comp_self_of_isotypic_three_eq_top ?_
  rw [isotypic_eq_top_iff]
  apply LinearMap.toMatrix'.injective
  simp [cyclotomic_three, pow_two, LinearMap.toMatrix'_mul, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Falsification: the `Φ₆` formula `J := 2σ - 1` is wrong on the `Φ₃` part. -/
example : ((2 : ℚ) • ρ₃ - 1).comp ((2 : ℚ) • ρ₃ - 1) ≠ (-3 : ℚ) • LinearMap.id := by
  intro h
  have := congrFun (congrFun (congrArg LinearMap.toMatrix' h) 1) 0
  norm_num [Matrix.vecHead, Matrix.vecTail] at this

/-- `-ρ₃` has order dividing 6. -/
example : (-ρ₃) ^ 6 = 1 := by
  apply LinearMap.toMatrix'.injective
  simp [pow_succ, LinearMap.toMatrix'_mul, Matrix.one_fin_two]

/-- All of `ℚ²` is the `Φ₆` part of `-ρ₃`. -/
example : isotypic (-ρ₃) 6 = ⊤ := by
  rw [isotypic_eq_top_iff]
  apply LinearMap.toMatrix'.injective
  simp [cyclotomic_six, pow_two, LinearMap.toMatrix'_mul, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- `J := 2(-ρ₃) - 1` squares to `-3` on `ℚ²`. -/
example : ((2 : ℚ) • -ρ₃ - 1).comp ((2 : ℚ) • -ρ₃ - 1) = (-3 : ℚ) • LinearMap.id := by
  refine two_smul_sub_one_comp_self_of_isotypic_six_eq_top ?_
  rw [isotypic_eq_top_iff]
  apply LinearMap.toMatrix'.injective
  simp [cyclotomic_six, pow_two, LinearMap.toMatrix'_mul, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- All of `ℚ²` is the `Φ₄` part of `ρ₄`. -/
example : isotypic ρ₄ 4 = ⊤ := by
  rw [isotypic_eq_top_iff]
  apply LinearMap.toMatrix'.injective
  simp [cyclotomic_four_rat, pow_two, LinearMap.toMatrix'_mul, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- `ρ₄ ∘ ρ₄ = -1`. -/
example : LinearMap.comp ρ₄ ρ₄ = (-1 : ℚ) • LinearMap.id := by
  refine comp_self_of_isotypic_four_eq_top ?_
  rw [isotypic_eq_top_iff]
  apply LinearMap.toMatrix'.injective
  simp [cyclotomic_four_rat, pow_two, LinearMap.toMatrix'_mul, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- The cyclic permutation `π₃` of `ℚ³` has order dividing 3. -/
example : π₃ ^ 3 = 1 := by
  apply LinearMap.toMatrix'.injective
  simp [pow_succ, LinearMap.toMatrix'_mul, Matrix.one_fin_three]

/-- The `Φ₁` part of `π₃` is the line spanned by `(1, 1, 1)`, of dimension 1. -/
example : isotypic π₃ 1 = Submodule.span ℚ {![1, 1, 1]} ∧
    Module.finrank ℚ (isotypic π₃ 1) = 1 := by
  have hπ (v : Fin 3 → ℚ) : π₃ v = ![v 2, v 0, v 1] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h : isotypic π₃ 1 = Submodule.span ℚ {![1, 1, 1]} := by
    ext v
    rw [mem_isotypic, cyclotomic_one, Submodule.mem_span_singleton]
    simp only [map_sub, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      hπ]
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      refine ⟨v 0, ?_⟩
      ext i; fin_cases i <;> simp [h1, h0]
    · rintro ⟨a, rfl⟩
      ext i; fin_cases i <;> simp
  refine ⟨h, ?_⟩
  rw [h, finrank_span_singleton]
  intro h0
  simpa using congrFun h0 0

/-- The `Φ₃` part of `π₃` is the plane `x + y + z = 0`, of dimension 2. -/
example : (∀ v : Fin 3 → ℚ, v ∈ isotypic π₃ 3 ↔ v 0 + v 1 + v 2 = 0) ∧
    Module.finrank ℚ (isotypic π₃ 3) = 2 := by
  have hJ : aeval π₃ (cyclotomic 3 ℚ) = Matrix.toLin' !![(1 : ℚ), 1, 1; 1, 1, 1; 1, 1, 1] := by
    apply LinearMap.toMatrix'.injective
    simp [cyclotomic_three, pow_two, LinearMap.toMatrix'_mul, Matrix.one_fin_three]
  have hmem (v : Fin 3 → ℚ) : v ∈ isotypic π₃ 3 ↔ v 0 + v 1 + v 2 = 0 := by
    rw [mem_isotypic, hJ]
    simp [funext_iff, Fin.forall_fin_succ, dotProduct, Fin.sum_univ_three]
  refine ⟨hmem, ?_⟩
  let f : (Fin 3 → ℚ) →ₗ[ℚ] ℚ :=
    (LinearMap.proj 0 : (Fin 3 → ℚ) →ₗ[ℚ] ℚ) + LinearMap.proj 1 + LinearMap.proj 2
  have hker : isotypic π₃ 3 = LinearMap.ker f := by
    ext v
    rw [hmem, LinearMap.mem_ker]
    rfl
  have hrange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr fun a => ⟨Pi.single 0 a, by simp [f]⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hrn
  rw [hker]
  omega

end Examples

end HodgeLean.Foundations

end

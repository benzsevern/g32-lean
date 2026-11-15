import HodgeLean.Adapters.AbelianCMDataProofs

/-! # The Powers flagship, stage G4: CM data from endomorphisms (FROZEN SPEC)

Stage G4 of formalizing PW v0.3, Theorem 4.2 (`thm:gen`), "Hodge classes on powers of abelian
varieties of Weil type and of type IV with exact endomorphism algebra"
(doi:10.5281/zenodo.23570103). Theorem 4.2's generators are the pullbacks `f_a^* W_k(A)` for
`a ∈ 𝒪^r`, where `𝒪` is an order of `L` acting on `A` and `f_a : A^r → A` is `x ↦ Σ a_i x_i`.
This stage packages that CM data on an actual abelian variety `A`, for any `ℚ`-algebra map
`θ : L →ₐ[ℚ] End⁰(A)` from a field `L`. Each theorem is proved by the matching `_aux` theorem in
`AbelianCMDataProofs.lean`; the definitions are in `AbelianCMDataDefs.lean`.

It claims:

* the named action `abelianEnd0Action` of `End⁰(A) = ℚ ⊗ End(A)` on `HQ A 1` is `q ⊗ f ↦ q • f^*`
  (into the opposite ring), is injective, and lands in the Hodge endomorphisms; the weight-one
  Hodge pieces of `A` are the lattice-side pieces `Hol`, `Anti`; so every element of `L` acts by
  a map preserving them (the input `hR` of PW-0's `spec_pw0_cmPowerSpan_le_rationalExteriorHodge`
  and the field `preserves` of `pwWeilAction`);
* `𝒪 = pwOrder A θ`: each `a ∈ 𝒪` comes from exactly one endomorphism `pwOrderEnd A θ a`, which
  acts as `θ(a)`; every `a ∈ L` has a multiple `N a ∈ 𝒪`, `N > 0`;
* for power data `P : AbelianPowerData A Y r` (biproduct identities, a stand-in for `Y = A^r`),
  `P.sumMap a = Σ a_i ∘ p_i` is a group homomorphism and pulls back on `H¹` to
  `Σ_i p_i^* ∘ a_i^*`;
* homogeneity: in every degree `n`, the `ℚ`-span of the pullbacks `⋀^n f_a^* W` in the model
  `⋀^n (H¹(A) ⊗ ℚ^r)` over `a ∈ 𝒪^r` equals the span over `a ∈ L^r`;
* agreement with PW-0: the model pullback at `a_i = p_i + s_i u` is `weilPowerPullback J p s` with
  `J = θ(u)^*`, the `J` of `pwWeilAction`; and at `L = ℚ(u)` the image of `L` is `ℚ[J]`, the `R`
  of PW-0's statements at `L = k`;
* degenerate cases: `r = 0` forces `H¹(Y) = 0`; `dim A = 0` forces `𝒪 = L` (so `𝒪` is an order
  only for `dim A > 0`); `a = 0` and the zero endomorphism give the zero pullback (`example`s).

It does not claim: that `𝒪` is finitely generated over `ℤ` or is an order for `dim A > 0`; that
`θ` exists for a given `A`, or `End⁰(A) = L`; the existence of `A^r` or of power data for `r ≥ 2`;
any statement in degrees `n ≥ 2` of `HQ Y`, which needs cup-product naturality (G1b, G2); the
comparison of the model `⋀ (H¹(A) ⊗ ℚ^r)` with `H^*(Y)` (G2); any Hodge-group, generation or
algebraicity statement. Implication from `θ` only where binders are stated. HC no distance; AV
milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower

namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]

/-- **The action of `End⁰(A)` on pure tensors**: `q ⊗ f` acts by `q • f^*`, in the opposite ring.
Source: Mumford, *Abelian Varieties*, §19 (`End⁰(X) = End(X) ⊗_ℤ ℚ`); Mathlib
`Algebra.TensorProduct.lift_tmul`; `abelianEnd0Action`. -/
theorem spec_g4_abelianEnd0Action_tmul (q : ℚ) (f : AbelianEnd A) :
    abelianEnd0Action A (q ⊗ₜ[ℤ] f) = MulOpposite.op (q • abelianEndAction A f) :=
  spec_g4_abelianEnd0Action_tmul_aux A q f

-- On `1 ⊗ f` it is G1a's `homPullback` along `f`.
example (f : AbelianEnd A) : (abelianEnd0Action A ((1 : ℚ) ⊗ₜ[ℤ] f)).unop = homPullback f.hom 1 := by
  rw [spec_g4_abelianEnd0Action_tmul, one_smul, MulOpposite.unop_op]
  rfl

/-- **The action of `End⁰(A)` is faithful.** It is the map of stage 1's `spec_abelianEnd0Action`
(an algebra map out of `ℚ ⊗ End(A)` is determined by its values on `1 ⊗ f`), which is injective.
Source: Mumford, *Abelian Varieties*, §19, Theorem 3 and Corollary 2; `spec_abelianEnd0Action`. -/
theorem spec_g4_abelianEnd0Action_injective : Function.Injective (abelianEnd0Action A) :=
  spec_g4_abelianEnd0Action_injective_aux A

example (x : AbelianEnd0 A) (hx : abelianEnd0Action A x = 1) : x = 1 :=
  spec_g4_abelianEnd0Action_injective A (hx.trans (map_one _).symm)

/-- **`End⁰(A)` acts by Hodge endomorphisms**: every `x ∈ End⁰(A)` acts on `HQ A 1` by a map whose
complexification preserves `Hol` and `Anti`. The generators `1 ⊗ f` do
(`spec_abelianEndAction_hodge`), and `hodgeEndH1 A` is a subalgebra.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 and Theorem 1.4.1;
`spec_abelianEndAction_hodge`, `hodgeEndH1`. -/
theorem spec_g4_abelianEnd0Action_mem_hodgeEndH1 (x : AbelianEnd0 A) :
    (abelianEnd0Action A x).unop ∈ hodgeEndH1 A :=
  spec_g4_abelianEnd0Action_mem_hodgeEndH1_aux A x

example (x : AbelianEnd0 A) :
    (complexHolomorphicH1 A).map ((abelianEnd0Action A x).unop.baseChange ℂ) ≤
      complexHolomorphicH1 A :=
  (spec_g4_abelianEnd0Action_mem_hodgeEndH1 A x).1

omit [IsCommMonObj A] in
/-- **The weight-one Hodge pieces of `A` are the lattice-side pieces**: `cohomologyHodgePiece A 1`
(the pieces of `abelianWeightOneHodgeStructure A`) is `Hol` in type `(1, 0)`, `Anti` in type
`(0, 1)` and `⊥` elsewhere. In type `(1, 0)` it is the pullback of `F^1 ⊓ conj F^0 = F^1`, which is
`Hol` (`spec_comap_hodgeFiltration_one_eq`); in type `(0, 1)` that of `conj F^1`, which is
`Anti`; in types `(p, 1 - p)` with `p ≥ 2` or `p ≤ -1` one of `F^p H¹`, `F^{1-p} H¹` is `0`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1
(`H^{1,0} = H^0(Ω¹)`); `spec_comap_hodgeFiltration_one_eq`,
`spec_comap_conjHodgeFiltration_one_eq_of_eq`, `hodgeFiltration_eq_top_of_nonpos`,
`hodgeFiltration_eq_bot_of_lt`. -/
theorem spec_g4_cohomologyHodgePiece_one_eq : cohomologyHodgePiece A 1 = latticeHodgePieces A :=
  spec_g4_cohomologyHodgePiece_one_eq_aux A

omit [IsCommMonObj A] in
example : cohomologyHodgePiece A 1 (2, -1) = ⊥ := by
  rw [spec_g4_cohomologyHodgePiece_one_eq]
  simp [latticeHodgePieces]

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **Every element of `L` preserves the Hodge pieces of `H¹(A)`**: for `x ∈ L`, the action
`θ(x)^*` maps each `cohomologyHodgePiece A 1 pq` into itself. By
`spec_g4_abelianEnd0Action_mem_hodgeEndH1` and `spec_g4_cohomologyHodgePiece_one_eq`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 and Theorem 1.4.1; PW v0.3,
Subsection 2.1 (`L` acts on the rational Hodge structure `V`). -/
theorem spec_g4_pwAction_map_le (θ : L →ₐ[ℚ] AbelianEnd0 A) (x : L) (pq : ℤ × ℤ) :
    (cohomologyHodgePiece A 1 pq).map ((pwAction A θ x).baseChange ℂ) ≤
      cohomologyHodgePiece A 1 pq :=
  spec_g4_pwAction_map_le_aux A θ x pq

/-- The input `hR` of PW-0's `spec_pw0_cmPowerSpan_le_rationalExteriorHodge` for
`R = pwActionRange A θ` on the weight-one structure of `A`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) :
    ∀ T ∈ pwActionRange A θ, ∀ pq, ∀ x ∈ cohomologyHodgePiece A 1 pq,
      (T : Module.End ℚ (HQ A 1)).baseChange ℂ x ∈ cohomologyHodgePiece A 1 pq := by
  rintro _ ⟨y, rfl⟩ pq x hx
  exact spec_g4_pwAction_map_le A θ y pq (Submodule.mem_map_of_mem hx)

-- The Weil action of `u` with `u² = -3` exists unconditionally, with `J = θ(u)^*`.
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3) :
    letI := (finiteBetti_abelian A).finite 1
    (pwWeilAction A θ u 3 hu (spec_g4_pwAction_map_le A θ u)).J = pwAction A θ u :=
  rfl

/-- **Each `a ∈ 𝒪` comes from exactly one endomorphism**: `1 ⊗ f = θ(a)` holds exactly for
`f = pwOrderEnd A θ a`. Existence is the definition of `𝒪`; uniqueness is the injectivity of
`f ↦ 1 ⊗ f`, as `End(A)` is torsion-free (it acts faithfully on the `ℚ`-space `HQ A 1`,
`spec_abelianEndAction_injective`).
Source: Mumford, *Abelian Varieties*, §19, Theorem 3 (`End(A)` is a free `ℤ`-module, so
`End(A) ⊆ End⁰(A)`); PW v0.3, Theorem 4.2 (the order `𝒪 ⊆ L` acting on `A`). -/
theorem spec_g4_tmul_eq_iff_pwOrderEnd (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : pwOrder A θ)
    (f : AbelianEnd A) : (1 : ℚ) ⊗ₜ[ℤ] f = θ a ↔ f = pwOrderEnd A θ a :=
  spec_g4_tmul_eq_iff_pwOrderEnd_aux A θ a f

-- `1 ∈ 𝒪` comes from the identity.
example (θ : L →ₐ[ℚ] AbelianEnd0 A) :
    pwOrderEnd A θ ⟨1, (pwOrder A θ).one_mem⟩ = 1 :=
  ((spec_g4_tmul_eq_iff_pwOrderEnd A θ _ 1).1
    (by rw [map_one, Algebra.TensorProduct.one_def])).symm

/-- **The chosen endomorphism acts as `θ(a)`**: `(pwOrderEnd A θ a)^* = pwAction A θ a`.
By `spec_g4_abelianEnd0Action_tmul` at `q = 1`.
Source: PW v0.3, Theorem 4.2 (`𝒪` acts on `A`, compatibly with the action of `L` on `V`);
`spec_g4_abelianEnd0Action_tmul`. -/
theorem spec_g4_abelianEndAction_pwOrderEnd (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : pwOrder A θ) :
    abelianEndAction A (pwOrderEnd A θ a) = pwAction A θ a :=
  spec_g4_abelianEndAction_pwOrderEnd_aux A θ a

-- The endomorphisms coming from `𝒪` commute on `HQ A 1`, as `L` is commutative.
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (a b : pwOrder A θ) :
    abelianEndAction A (pwOrderEnd A θ a) * abelianEndAction A (pwOrderEnd A θ b) =
      abelianEndAction A (pwOrderEnd A θ b) * abelianEndAction A (pwOrderEnd A θ a) := by
  rw [spec_g4_abelianEndAction_pwOrderEnd, spec_g4_abelianEndAction_pwOrderEnd, ← map_mul,
    ← map_mul, mul_comm]

/-- **Clearing denominators**: every `a ∈ L` has a multiple `N a ∈ 𝒪` with `N > 0`. Every element
of `ℚ ⊗[ℤ] End(A)` is `(1 / s) ⊗ f` for some `s ≠ 0` (`ℚ ⊗[ℤ] M` is the localization of `M` at
`ℤ ∖ {0}`), so `|s| • θ(a) = 1 ⊗ (± f)`.
Source: Mumford, *Abelian Varieties*, §19 (`End⁰(A) = End(A) ⊗ ℚ`); Mathlib
`IsLocalizedModule.mk'_surjective`, `TensorProduct.isBaseChange`. -/
theorem spec_g4_exists_nat_mul_mem_pwOrder (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : L) :
    ∃ N : ℕ, 0 < N ∧ (N : L) * a ∈ pwOrder A θ :=
  spec_g4_exists_nat_mul_mem_pwOrder_aux A θ a

-- `𝒪` contains the integers; so for `a ∈ ℚ ⊆ L` the statement is the usual denominator.
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (n : ℤ) : (n : L) ∈ pwOrder A θ :=
  intCast_mem (pwOrder A θ) n

/-- **Falsification: for `dim A = 0`, `𝒪` is all of `L`.** Then `HQ A 1 = 0`
(`spec_complexH1_dimension`, `spec_complexH1_split`), so `End(A) = 0` by faithfulness, hence
`End⁰(A) = 0` and every `θ(a)` is `1 ⊗ 0`. So "`𝒪` is an order of `L`" (finitely generated over
`ℤ`) fails without `dim A > 0` whenever `L ≠ ℚ`; here `θ` is the zero map into the zero ring.
Source: Mumford, *Abelian Varieties*, §19, Theorem 3; `spec_abelianEndAction_injective`,
`spec_complexH1_dimension`. -/
theorem spec_g4_pwOrder_eq_top_of_dim_eq_zero (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (h0 : dim A.left = 0) : pwOrder A θ = ⊤ :=
  spec_g4_pwOrder_eq_top_of_dim_eq_zero_aux A θ h0

example (θ : L →ₐ[ℚ] AbelianEnd0 A) (h0 : dim A.left = 0) (a : L) : a ∈ pwOrder A θ := by
  rw [spec_g4_pwOrder_eq_top_of_dim_eq_zero A θ h0]
  trivial

section Power

variable {A} {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
  [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}

omit [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] in
/-- **`f_a` is a group homomorphism.** `P.sumMap a = Σ a_i ∘ p_i : Y ⟶ A` is a homomorphism of
group objects for every `a ∈ End(A)^r`: each `p_i ≫ a_i` is one, and in the commutative group
`A` products of homomorphisms are homomorphisms.
Source: PW v0.3, Theorem 4.2 (`f_a : A^r → A` is a homomorphism); Mumford, *Abelian Varieties*,
§4; Mathlib `IsMonHom`, `Hom.mul_def`. -/
theorem spec_g4_isMonHom_sumMap (P : AbelianPowerData A Y r) (a : Fin r → AbelianEnd A) :
    IsMonHom (P.sumMap a) :=
  spec_g4_isMonHom_sumMap_aux P a

omit [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] in
-- For `a ∈ 𝒪^r` this is Theorem 4.2's `f_a`.
example {L : Type*} [Field L] [Algebra ℚ L] (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (P : AbelianPowerData A Y r) (a : Fin r → pwOrder A θ) : IsMonHom (P.pwSumMap θ a) :=
  spec_g4_isMonHom_sumMap P _

/-- **The pullback of `f_a` on `H¹`**: `(Σ a_i ∘ p_i)^* = Σ_i p_i^* ∘ a_i^*`. By G1a's additivity
(`spec_homPullback_mul`, `spec_homPullback_one`, for all morphisms) and functoriality
(`spec_homPullback_comp`).
Source: PW v0.3, Theorem 4.2 and its proof, paragraph "Weil classes"; Birkenhake–Lange, *Complex
Abelian Varieties*, 2nd ed., §1.2; `spec_homPullback_mul`, `spec_homPullback_comp`. -/
theorem spec_g4_homPullback_sumMap (P : AbelianPowerData A Y r) (a : Fin r → AbelianEnd A) :
    homPullback (P.sumMap a) 1 = ∑ i, homPullback (P.proj i) 1 ∘ₗ abelianEndAction A (a i) :=
  spec_g4_homPullback_sumMap_aux P a

-- `a = 0`: the zero homomorphism pulls back to `0`.
example (P : AbelianPowerData A Y r) : homPullback (P.sumMap 0) 1 = 0 := by
  rw [spec_g4_homPullback_sumMap]
  simp [spec_abelianEndAction_zero]

-- For `a ∈ 𝒪^r`, the coefficients are the actions of `L`.
example {L : Type*} [Field L] [Algebra ℚ L] (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (P : AbelianPowerData A Y r) (a : Fin r → pwOrder A θ) :
    homPullback (P.pwSumMap θ a) 1 = ∑ i, homPullback (P.proj i) 1 ∘ₗ pwAction A θ (a i) := by
  simp only [AbelianPowerData.pwSumMap, spec_g4_homPullback_sumMap,
    spec_g4_abelianEndAction_pwOrderEnd]

omit [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] in
/-- **Falsification: `r = 0`.** Power data with no factors forces `𝟙 Y = 1` (the empty product),
so `id = 𝟙 Y^* = 1^* = 0` on `HQ Y 1` (`spec_homPullback_id`, `spec_homPullback_one`) and
`H¹(Y) = 0`. So the biproduct identities are not vacuous: `Y` must be a point up to `H¹`.
Source: Mac Lane, *Categories for the Working Mathematician*, §VIII.2 (the empty biproduct is the
zero object); `spec_homPullback_id`, `spec_homPullback_one`. -/
theorem spec_g4_eq_zero_of_powerData_zero (P : AbelianPowerData A Y 0) (y : HQ Y 1) :
    y = 0 :=
  spec_g4_eq_zero_of_powerData_zero_aux P y

omit [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] in
example (P : AbelianPowerData A Y 0) : Subsingleton (HQ Y 1) :=
  ⟨fun y y' => (spec_g4_eq_zero_of_powerData_zero P y).trans
    (spec_g4_eq_zero_of_powerData_zero P y').symm⟩

end Power

/-- **Homogeneity: the span over `𝒪^r` is the span over `L^r`.** In each degree `n`, the
`ℚ`-span of the classes `⋀^n (f_a^*) w`, `w ∈ W`, in the model `⋀^n (H¹(A) ⊗ ℚ^r)`, is the same for
`a ∈ 𝒪^r` and for `a ∈ L^r`. For `a ∈ L^r` take `N > 0` with `N a ∈ 𝒪^r`
(`spec_g4_exists_nat_mul_mem_pwOrder`, a common multiple); `f_{N a}^* = N • f_a^*`, so
`⋀^n f_{N a}^* = N^n • ⋀^n f_a^*` and `N^n ≠ 0` in `ℚ`.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes" (the classes `f_a^* w` are
homogeneous of degree `n` in `a`, so `𝒪` may replace `L`). -/
theorem spec_g4_span_pwOrder_eq (θ : L →ₐ[ℚ] AbelianEnd0 A) (r : ℕ) {n : ℕ}
    (W : Submodule ℚ (⋀[ℚ]^n (HQ A 1))) :
    Submodule.span ℚ {y | ∃ a : Fin r → L, (∀ i, a i ∈ pwOrder A θ) ∧
        ∃ w ∈ W, exteriorPower.map n (pwPowerPullback A θ a) w = y} =
      Submodule.span ℚ {y | ∃ a : Fin r → L,
        ∃ w ∈ W, exteriorPower.map n (pwPowerPullback A θ a) w = y} :=
  spec_g4_span_pwOrder_eq_aux A θ r W

-- Every generator over `L^r` lies in the span over `𝒪^r`.
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (r : ℕ) {n : ℕ} (W : Submodule ℚ (⋀[ℚ]^n (HQ A 1)))
    (a : Fin r → L) (v : ⋀[ℚ]^n (HQ A 1)) (hv : v ∈ W) :
    exteriorPower.map n (pwPowerPullback A θ a) v ∈
      Submodule.span ℚ {y | ∃ a : Fin r → L, (∀ i, a i ∈ pwOrder A θ) ∧
        ∃ w ∈ W, exteriorPower.map n (pwPowerPullback A θ a) w = y} := by
  rw [spec_g4_span_pwOrder_eq]
  exact Submodule.subset_span ⟨a, v, hv, rfl⟩

/-- **Agreement with PW-0's Weil pullbacks**: at `a_i = p_i + s_i u`, the model pullback is
`weilPowerPullback J p s : x ↦ x ⊗ p + J x ⊗ s` with `J = θ(u)^*`, the `J` of `pwWeilAction`. So
`cmPowerPullback` over the image of `L` restricts, on the coefficients `ℚ + ℚ u`, to the
pullbacks of `divisorPulledWeilSpan`. No relation on `u` is used.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes"; F-1575 / TR54 §3;
`spec_pw0_cmPowerPullback_adjoin`, `weilPowerPullback`. -/
theorem spec_g4_pwPowerPullback_eq_weilPowerPullback (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    {r : ℕ} (p s : Fin r → ℚ) :
    pwPowerPullback A θ (fun i => algebraMap ℚ L (p i) + algebraMap ℚ L (s i) * u) =
      weilPowerPullback (pwAction A θ u) p s :=
  spec_g4_pwPowerPullback_eq_weilPowerPullback_aux A θ u p s

-- The same with `J` read off `pwWeilAction`, for `u² = -3`.
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3) {r : ℕ}
    (p s : Fin r → ℚ) :
    letI := (finiteBetti_abelian A).finite 1
    pwPowerPullback A θ (fun i => algebraMap ℚ L (p i) + algebraMap ℚ L (s i) * u) =
      weilPowerPullback (pwWeilAction A θ u 3 hu (spec_g4_pwAction_map_le A θ u)).J p s :=
  spec_g4_pwPowerPullback_eq_weilPowerPullback A θ u p s

/-- **Degenerate check `L = k`**: if `L = ℚ(u)`, the image of `L` in `Module.End ℚ (HQ A 1)` is
`ℚ[J]`, `J = θ(u)^*`. So PW-0's statements at `R = Algebra.adjoin ℚ {J}`
(`spec_pw0_gkLie_adjoin_eq`, `spec_pw0_cmPowerSpan_adjoin_eq`,
`spec_pw0_rationalExteriorHodge_eq_cmPowerSpan`) apply to `R = pwActionRange A θ`.
Source: PW v0.3, proof of Theorem 3.1, first paragraph (`L = k`); Mathlib
`AlgHom.map_adjoin_singleton`. -/
theorem spec_g4_pwActionRange_eq_adjoin (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : Algebra.adjoin ℚ {u} = ⊤) :
    pwActionRange A θ = Algebra.adjoin ℚ {pwAction A θ u} :=
  spec_g4_pwActionRange_eq_adjoin_aux A θ u hu

example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : Algebra.adjoin ℚ {u} = ⊤)
    (E : LinearMap.BilinForm ℚ (HQ A 1)) :
    gkLie E (pwActionRange A θ) (pwAction A θ u) = weilSU E (pwAction A θ u) := by
  rw [spec_g4_pwActionRange_eq_adjoin A θ u hu]
  exact spec_pw0_gkLie_adjoin_eq E _

end HodgeLean.Adapters

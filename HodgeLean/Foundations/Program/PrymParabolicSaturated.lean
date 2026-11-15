import HodgeLean.Foundations.Program.PrymParabolicSaturatedProofs

/-! # Stage H5, first part: the saturated cellular lattice and the isotypic comparison (FROZEN SPEC)

The frozen spec for `docs/briefs/cloud-spec-h5.md` (`docs/specs/PrymParabolicSaturated.md`). Do not
edit this file. Each theorem restates the matching `_aux` theorem in
`PrymParabolicSaturatedProofs.lean`.

**Claimed (once the bodies are proved).** For the G32 root `b4b_root` and the lifted complex
`X̃(b4b_root)` of stages H3a–H3b:
- the saturation `L` of `range hg2_projector` in cellular `H₁(X̃; ℤ)` is free of rank `12`;
- the central element (matrix `ω·1`) preserves `L` (a body in the Defs file), and `1 + 2Z`
  squares to `−3` on `L`;
- for any `ℤ`-linear equivalence `e : M ≃ N` intertwining two families of maps indexed by
  `b4b_Group`, `e` carries the saturated image of the primitive operator of the first family onto
  that of the second and intertwines the central operators; for every fibre of the B6-3 family and
  every deck-equivariant `e : H₁^cell(X̃) ≃ H₁^sing(fibre)` this sends `L` onto
  `b63l_parameterLattice … t` and the cellular centre to `b63d_centre` (chain check);
- the isotypic comparison over `K = ℚ(√−3)`: the evaluation of the `0`-th coordinate of
  `hg4_sigmaK`-equivariant cocycles on `L` is a `K`-linear bijection from `H¹_σ` onto the
  functionals `φ` on `ℚ ⊗ L` with `φ ∘ (1 + 2Z) = √−3 · φ`, the `K`-linear dual of `ℚ ⊗ L`
  for the `K`-structure given by `1 + 2Z`;
- the coordinate cup comparison: on `hg4_sigmaK`-equivariant cochains the scalar cup product of
  coordinates `i, j` on the orientation chain is `δ_ij / 4` times H4's cup form `hg4_cupForm`;
- `L` is not stable under the full deck group: the primitive projector selects a coordinate line
  and is not central, so the compatibility is with the centre only.
The chain checks give the cellular analogue of `b64b_lattice_hermitian`'s operator data, the
transport onto `b63l_parameterLattice` with the centre, and, toward `g32d_ParabolicPolarization`,
Gram matrix `|G|·g32H0 ζ` for `4(1 + 2ζ)` times the scalar `0`-coordinate cup product on the
Shapiro cocycles of H6's certificate.

**Not claimed.** The existence of a deck-equivariant isomorphism between cellular and singular
`H₁` of a fibre (H3b steps C–D, drafted separately); that the scalar cup product is the
intersection form (the geometric half of H4: Poincaré duality on the explicit surface, with the
sign of the orientation chain); any comparison with `b63e_singularQ` or the Weil Hermitian form of
a fibre; any discriminant (H7). The statements are an implication from the stated algebraic
hypotheses only. The tuple is the repository's `b4b_root`, not identified with the monodromy at
the paper's base point `C₀`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open HodgeLean.Papers CategoryTheory AlgebraicTopology.Singular Matrix
open scoped TensorProduct Manifold ContDiff

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-! ## The saturated cellular lattice -/

/-- **The saturated cellular lattice is free of rank twelve.** `H₁(X̃(b4b_root); ℤ)` is free and
finite (`hg2_H1_rank`), so the saturation of a submodule is free of the same rank as the
submodule, here `12` (`hg2_projector_rank`). The cellular analogue of `b63d_lattice_rank`.
Source: Bourbaki, *Algebra*, Ch. VII, §3 (submodules of free modules over a principal ideal
domain); Birkenhake–Lange, *Complex Abelian Varieties*, §12.2. -/
theorem hg6_cellLattice_basis : Nonempty (Module.Basis (Fin 12) ℤ hg6_cellLattice) :=
  hg6_cellLattice_basis_aux

example : Nonempty (Module.Basis (Fin 12) ℤ hg6_cellLattice) := hg6_cellLattice_basis

/-- **`1 + 2Z` squares to `−3` on the saturated cellular lattice.** With `Z` the action of the
central element `z₀` of matrix `ω·1`: `(1 + Z + Z²)·hg2_projector = Σ_k (c_k + c_{z₀⁻¹k} +
c_{z₀⁻²k}) k_*`, and `c_{z₀⁻ᵐk} = 6 Re(ωᵐ ρ(k⁻¹)₀₀)` (`b63d_projectorCoeff_complex`), so the
coefficients sum to `6 Re((1 + ω + ω²) ρ(k⁻¹)₀₀) = 0`; the relation passes to the saturation
because `H₁` is torsion-free. Then `(1 + 2Z)² = 4(1 + Z + Z²) − 3`. The cellular analogue of
`b63d_prymOperator_sq`.
Source: G32 v0.16, §3.2–3.3; Serre, *Linear Representations of Finite Groups*, §2.2. -/
theorem hg6_cellOperator_sq (x : hg6_cellLattice) :
    hg6_cellOperator (hg6_cellOperator x) = (-3 : ℤ) • x :=
  hg6_cellOperator_sq_aux x

example (x : hg6_cellLattice) : hg6_cellOperator (hg6_cellOperator x) = (-3 : ℤ) • x :=
  hg6_cellOperator_sq x

/-! ## Transport of the saturated lattice and the centre -/

/-- **An intertwining equivalence carries the saturated image and the centre.** For any two
families `ρ, ρ'` of `ℤ`-linear maps indexed by `b4b_Group` and any `ℤ`-linear equivalence `e`
with `e ∘ ρ(h) = ρ'(h) ∘ e` for every `h`: `e` maps the saturation of the image of
`Σ_h b4b_projectorCoeff h · ρ(h)` onto the saturation of the image of the same combination of the
`ρ'(h)`, and intertwines the central operators. No hypothesis on `ρ, ρ'` beyond the intertwining
is needed.
Source: Bourbaki, *Algebra*, Ch. II, §1 (images under isomorphisms) and Ch. VII, §1
(saturation); `hg6_projOf`, `hg6_centreOf`. -/
theorem hg6_saturated_transport {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (ρ : b4b_Group → M →ₗ[ℤ] M) (ρ' : b4b_Group → N →ₗ[ℤ] N) (e : M ≃ₗ[ℤ] N)
    (he : ∀ h x, e (ρ h x) = ρ' h (e x)) :
    (b63l_saturation (LinearMap.range (hg6_projOf ρ))).map (e : M →ₗ[ℤ] N) =
        b63l_saturation (LinearMap.range (hg6_projOf ρ')) ∧
      ∀ x, e (hg6_centreOf ρ x) = hg6_centreOf ρ' (e x) :=
  hg6_saturated_transport_aux ρ ρ' e he

example {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (ρ : b4b_Group → M →ₗ[ℤ] M) (ρ' : b4b_Group → N →ₗ[ℤ] N) (e : M ≃ₗ[ℤ] N)
    (he : ∀ h x, e (ρ h x) = ρ' h (e x)) :
    (b63l_saturation (LinearMap.range (hg6_projOf ρ))).map (e : M →ₗ[ℤ] N) =
        b63l_saturation (LinearMap.range (hg6_projOf ρ')) ∧
      ∀ x, e (hg6_centreOf ρ x) = hg6_centreOf ρ' (e x) :=
  hg6_saturated_transport ρ ρ' e he

/-! ## The isotypic comparison over `K` -/

/-- **The isotypic comparison on the saturated rational lattice.** There is a `K`-linear injection
`Θ` from `H¹_σ` of the `K`-form `σ = hg4_sigmaK` to the `ℚ`-linear functionals `ℚ ⊗ L → K`, given
on representatives by `Θ [c] (1 ⊗ [z]) = ⟨c, z⟩₀`, the `0`-th coordinate of `Σ_ε z(ε) c(ε)`; its
image is exactly the functionals `φ` with `φ ∘ (1 + 2Z) = √−3 · φ`. Here `σ(z₀) = ζ·1`, so
`⟨c, Z z⟩ = ζ ⟨c, z⟩` and `1 + 2ζ = √−3`. Injective: `Σ_h c_h σ(h) = (3|G|/4) E₀₀` (Schur
orthogonality, with `ρ̄ ≇ ρ`), so `Θ[c] = 0` forces `⟨c, w⟩₀ = 0` on all of `H₁`, hence
`⟨c, w⟩ = 0` by irreducibility, hence `[c] = 0` by universal coefficients and averaging. Both
sides have `K`-dimension `6` (`hp_vparK_finrank`; rank `12` and `(1 + 2Z)² = −3`).
Source: G32 v0.16, Proposition 6.1 (steps 1, 2 and 4: the Prym part as `Hom_G` of the
representation into cohomology) and lines 537–548; Serre, §2.2 and §2.6; Hatcher, §3.1. -/
theorem hg6_isotypic_comparison :
    ∃ Θ : hg_eqH1 hg4_sigmaK b4b_root →ₗ[hp_K] ((ℚ ⊗[ℤ] hg6_cellLattice) →ₗ[ℚ] hp_K),
      Function.Injective Θ ∧
      (∀ φ, φ ∈ LinearMap.range Θ ↔
        ∀ x, φ (hg6_cellJ x) = QuadraticAlgebra.omega * φ x) ∧
      ∀ (c : hg_eqCocycles hg4_sigmaK b4b_root) (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
        (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
        Θ (Submodule.Quotient.mk c) ((1 : ℚ) ⊗ₜ[ℤ] ⟨Submodule.Quotient.mk z, hz⟩) =
          hg6_pairVec c.1 z.1 0 :=
  hg6_isotypic_comparison_aux

example :
    ∃ Θ : hg_eqH1 hg4_sigmaK b4b_root →ₗ[hp_K] ((ℚ ⊗[ℤ] hg6_cellLattice) →ₗ[ℚ] hp_K),
      Function.Injective Θ ∧
      (∀ φ, φ ∈ LinearMap.range Θ ↔
        ∀ x, φ (hg6_cellJ x) = QuadraticAlgebra.omega * φ x) ∧
      ∀ (c : hg_eqCocycles hg4_sigmaK b4b_root) (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
        (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
        Θ (Submodule.Quotient.mk c) ((1 : ℚ) ⊗ₜ[ℤ] ⟨Submodule.Quotient.mk z, hz⟩) =
          hg6_pairVec c.1 z.1 0 :=
  hg6_isotypic_comparison

/-- **The coordinate cup product is a quarter of H4's cup form (Schur).** For
`hg4_sigmaK`-equivariant `1`-cochains `α, β` (cocycles or not), the matrix
`M_ij = ⟨star α_i ∪ β_j, Σ_x Σ_i (A_i(x) − B_i(x))⟩` satisfies `M = σ̄(h) M σ̄(h)⁻¹` for every
`h` (the orientation chain is deck-invariant, and `σ` is unitary for the standard form), so it is
scalar since `σ̄` is absolutely irreducible; its trace is `hg4_cupForm b4b_root 1 α β`. Hence
`M_ij = δ_ij · hg4_cupForm / 4`.
Source: Serre, *Linear Representations of Finite Groups*, §2.2 (Schur's lemma); Hatcher, §3.2;
G32 v0.16, proof of Proposition 6.1 (the factorization `h_V ⊗ ψ`). -/
theorem hg6_coordCup_schur (α β : hg_Edge b4b_Group 13 → Fin 4 → hp_K)
    (hα : α ∈ hg_eqCochain1 hg4_sigmaK) (hβ : β ∈ hg_eqCochain1 hg4_sigmaK) (i j : Fin 4) :
    hg6_coordCup b4b_root i j α β =
      if i = j then (4 : hp_K)⁻¹ * hg4_cupForm b4b_root 1 α β else 0 :=
  hg6_coordCup_schur_aux α β hα hβ i j

example (α β : hg_Edge b4b_Group 13 → Fin 4 → hp_K)
    (hα : α ∈ hg_eqCochain1 hg4_sigmaK) (hβ : β ∈ hg_eqCochain1 hg4_sigmaK) (i j : Fin 4) :
    hg6_coordCup b4b_root i j α β =
      if i = j then (4 : hp_K)⁻¹ * hg4_cupForm b4b_root 1 α β else 0 :=
  hg6_coordCup_schur α β hα hβ i j

/-! ## Centre compatibility, not full equivariance -/

/-- **The saturated cellular lattice is not stable under the full deck group.** For `z ∈ L` and
`c ∈ H¹_σ`, `⟨c, z⟩` lies on the line `K e₀` (`Σ_h c_h σ(h) = (3|G|/4) E₀₀`); some `z ∈ L` has
`⟨c, z⟩₀ ≠ 0` (statement 4 with `H¹_σ ≠ 0`). If every `h_*` preserved `L`, then
`σ(h) e₀ ∈ K e₀` for every `h`, a `σ`-stable line, which the irreducible `σ` does not have.
Source: G32 v0.16, Definition 3.2 (the primitive projector onto the first coordinate line);
Serre, §2.2 and §2.6. -/
theorem hg6_lattice_not_deck_stable :
    ∃ h : b4b_Group, ∃ x ∈ hg6_cellLattice, hg2_H1act ℤ b4b_root h x ∉ hg6_cellLattice :=
  hg6_lattice_not_deck_stable_aux

example :
    ∃ h : b4b_Group, ∃ x ∈ hg6_cellLattice, hg2_H1act ℤ b4b_root h x ∉ hg6_cellLattice :=
  hg6_lattice_not_deck_stable

/-! ## Satisfiable, non-degenerate instances -/

/-- The action of the central element as a `ℤ`-linear automorphism of cellular `H₁`, with
inverse the action of its inverse (`hg2_H1act_mul`, `hg2_H1act_one`).
Source: Hatcher, *Algebraic Topology*, §1.3 and §2.1 (deck transformations act on homology). -/
def hg6_centreEquiv : hg2_H1 ℤ b4b_root ≃ₗ[ℤ] hg2_H1 ℤ b4b_root :=
  LinearEquiv.ofLinearMap (hg2_H1act ℤ b4b_root b63d_scalarElement)
    (hg2_H1act ℤ b4b_root b63d_scalarElement⁻¹)
    (by rw [hg2_H1act_mul, mul_inv_cancel, hg2_H1act_one])
    (by rw [hg2_H1act_mul, inv_mul_cancel, hg2_H1act_one])

example (x : hg2_H1 ℤ b4b_root) :
    hg6_centreEquiv x = hg2_H1act ℤ b4b_root b63d_scalarElement x := rfl

/-- **A non-trivial instance of statement 3.** The central element is itself an intertwining
automorphism of cellular `H₁` (it is central), so it maps the saturated cellular lattice, which
has rank `12` (statement 1), onto itself. -/
theorem hg6_centre_map_lattice :
    hg6_cellLattice.map (hg6_centreEquiv : hg2_H1 ℤ b4b_root →ₗ[ℤ] hg2_H1 ℤ b4b_root) =
      hg6_cellLattice := by
  have he : ∀ h x, hg6_centreEquiv (hg2_H1act ℤ b4b_root h x) =
      hg2_H1act ℤ b4b_root h (hg6_centreEquiv x) := fun h x => by
    change hg2_H1act ℤ b4b_root b63d_scalarElement (hg2_H1act ℤ b4b_root h x) =
      hg2_H1act ℤ b4b_root h (hg2_H1act ℤ b4b_root b63d_scalarElement x)
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hg2_H1act_mul, hg2_H1act_mul,
      hg6_scalar_comm _ _ b63d_scalarElement_matrix]
  exact (hg6_saturated_transport _ _ hg6_centreEquiv he).1

/-- **The centre acts non-trivially on `L`** (rules out the degenerate case `Z = 1`, where
`1 + 2Z = 3` would square to `9`): from statements 1 and 2, since `L ≠ 0` is torsion-free. -/
theorem hg6_cellCentreL_ne_id : hg6_cellCentreL ≠ LinearMap.id := by
  intro hZ
  obtain ⟨B⟩ := hg6_cellLattice_basis
  have hx := hg6_cellOperator_sq (B 0)
  have h3 : ∀ y, hg6_cellOperator y = (3 : ℤ) • y := fun y => by
    simp only [hg6_cellOperator, hZ, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smul_apply]
    module
  rw [h3, h3, smul_smul] at hx
  have h12 : (12 : ℤ) • B 0 = 0 := by
    have : ((3 : ℤ) * 3) • B 0 - (-3 : ℤ) • B 0 = 0 := by rw [hx, sub_self]
    rw [← sub_smul] at this
    norm_num at this ⊢
    exact this
  have h : B.repr ((12 : ℤ) • B 0) 0 = 0 := by
    rw [h12, LinearEquiv.map_zero, Finsupp.zero_apply]
  rw [LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same] at h
  norm_num at h

/-- **`H¹_σ` of the `K`-form has `K`-dimension `6`**, so the comparison of statement 4 is between
non-zero spaces: from `hg4_shapiroH1_bijective`, `hg4_sigmaK_tuple` and `hp_vparK_finrank`. -/
theorem hg6_eqH1_finrank : Module.finrank hp_K (hg_eqH1 hg4_sigmaK b4b_root) = 6 := by
  rw [← (LinearEquiv.ofBijective _ (hg4_shapiroH1_bijective hg4_sigmaK b4b_root
    b63d_root_product)).finrank_eq, hg4_sigmaK_tuple, hp_vparK_finrank]

example : Module.finrank hp_K (hg_eqH1 hg4_sigmaK b4b_root) ≠ 0 := by
  rw [hg6_eqH1_finrank]; norm_num

/-- **Centre compatibility, honestly.** The central element preserves `L`, while some deck
element does not (statements 3 and 6). -/
example : hg6_cellLattice.map (hg6_centreEquiv : hg2_H1 ℤ b4b_root →ₗ[ℤ] hg2_H1 ℤ b4b_root) =
      hg6_cellLattice ∧
    ∃ h : b4b_Group, ∃ x ∈ hg6_cellLattice, hg2_H1act ℤ b4b_root h x ∉ hg6_cellLattice :=
  ⟨hg6_centre_map_lattice, hg6_lattice_not_deck_stable⟩

/-! ## Chain checks -/

/-- **Chain check toward `b63l_parameterLattice` (H3b step D attaches here).** For every fibre of
the B6-3 family and every `ℤ`-linear equivalence `e` from cellular `H₁(X̃(b4b_root); ℤ)` to
singular `H₁` of the fibre that intertwines the deck actions, `e` maps the saturated cellular
lattice onto `b63l_parameterLattice … t` and the cellular centre to `b63d_centre`. From
statement 3; the existence of such an `e` is not claimed. -/
theorem hg6_parameterLattice_transport (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    (e : hg2_H1 ℤ b4b_root ≃ₗ[ℤ] b6m_H1 (b63l_parameterFibre b C V hV t))
    (he : ∀ h x, e (hg2_H1act ℤ b4b_root h x) =
      homologyMap ℤ 1 (TopCat.ofHom (b6m_deck b b4b_Group C hC ⟨t.val, hV t.property⟩ h))
        (e x)) :
    hg6_cellLattice.map (e : hg2_H1 ℤ b4b_root →ₗ[ℤ] _) = b63l_parameterLattice b C hC V hV t ∧
      ∀ x, e (hg6_cellCentre x) = b63d_centre b C hC V hV t (e x) :=
  by
  have hdeck : ∀ h : b4b_Group,
      TopCat.ofHom (b6m_deck b b4b_Group C hC ⟨t.val, hV t.property⟩ h) =
        TopCat.ofHom (⟨fun x : b63l_parameterFibre b C V hV t ↦ h • x,
          (b6m_deck b b4b_Group C hC ⟨t.val, hV t.property⟩ h).continuous⟩ :
          C(b63l_parameterFibre b C V hV t, b63l_parameterFibre b C V hV t)) := fun h => rfl
  have hop : hg6_projOf (fun h => homologyMap ℤ 1
      (TopCat.ofHom (b6m_deck b b4b_Group C hC ⟨t.val, hV t.property⟩ h))) =
      b63l_fibreOperator b C hC ⟨t.val, hV t.property⟩ := by
    simp only [hg6_projOf, hdeck]
    rfl
  obtain ⟨h1, h2⟩ := hg6_saturated_transport (hg2_H1act ℤ b4b_root)
    (fun h => homologyMap ℤ 1
      (TopCat.ofHom (b6m_deck b b4b_Group C hC ⟨t.val, hV t.property⟩ h))) e he
  refine ⟨?_, h2⟩
  rw [hop] at h1
  exact h1

/-- **Chain check toward `g32d_ParabolicPolarization`.** On the Shapiro cocycles of H6's
`K`-certificate, `4(1 + 2ζ)` times the scalar cup product of the `0`-th coordinates has Gram matrix
`|G|·g32H0 ζ`: the field, Gram shape and positive rational scale `c = |G|` of the field, now on the
scalar coordinate that statement 4 evaluates on `L`. From statement 5 with `i = j = 0`,
`hg4_cupH1_mk`, `hg4_cupH1_shapiro`, `pc_SPar_mk` and `hp_certK_gram`. -/
theorem hg6_coordCup_gram (a b : Fin 6) :
    (1 + 2 * pc_zeta) * (4 * hg6_coordCup b4b_root 0 0
        (hg_shapiroCochain hg4_sigmaK b4b_root (hp_certK a))
        (hg_shapiroCochain hg4_sigmaK b4b_root (hp_certK b))) =
      (Fintype.card b4b_Group : hp_K) * g32H0 pc_zeta a b := by
  have hstar : Function.Semiconj hp_embed star star := hp_embed_star
  have hinv : ∀ x, (hg4_sigmaK x)ᴴ * 1 * hg4_sigmaK x = 1 := fun x => by
    apply hg4_embedMatrix_injective
    change ((hg4_sigmaK x)ᴴ * 1 * hg4_sigmaK x).map hp_embed = (1 : Matrix _ _ hp_K).map hp_embed
    rw [Matrix.mul_one, Matrix.map_mul, Matrix.conjTranspose_map _ hstar, hg4_sigmaK_map,
      Matrix.map_one _ (map_zero _) (map_one _), ← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp (b63l_toMatrix_mem_unitary _)
  have hprod := b63d_root_product
  have hprodT : (List.ofFn (pc_tuple hg4_sigmaK b4b_root)).prod = 1 := by
    have : List.ofFn (pc_tuple hg4_sigmaK b4b_root) = (List.ofFn b4b_root).map hg4_sigmaK := by
      rw [List.map_ofFn]
      rfl
    rw [this, ← map_list_prod, hprod, map_one]
  have hmem : ∀ a, hp_certK a ∈ pc_Z (pc_tuple hg4_sigmaK b4b_root) := fun a =>
    hg4_sigmaK_tuple ▸ hp_certK_mem a
  have hgram : (1 + 2 * pc_zeta) *
      pc_S (pc_tuple hg4_sigmaK b4b_root) 1 (hp_certK a) (hp_certK b) = g32H0 pc_zeta a b := by
    rw [hg4_sigmaK_tuple]
    exact hp_certK_gram a b
  let α := hg4_shapiroZ hg4_sigmaK b4b_root ⟨hp_certK a, hmem a⟩
  let β := hg4_shapiroZ hg4_sigmaK b4b_root ⟨hp_certK b, hmem b⟩
  have hα : (α : hg_Edge b4b_Group 13 → Fin 4 → hp_K) ∈ hg_eqCochain1 hg4_sigmaK :=
    (Submodule.mem_inf.mp α.2).1
  have hβ : (β : hg_Edge b4b_Group 13 → Fin 4 → hp_K) ∈ hg_eqCochain1 hg4_sigmaK :=
    (Submodule.mem_inf.mp β.2).1
  have hcup : hg4_cupForm b4b_root 1 (α : hg_Edge b4b_Group 13 → Fin 4 → hp_K) β =
      (Fintype.card b4b_Group : hp_K) *
        pc_S (pc_tuple hg4_sigmaK b4b_root) 1 (hp_certK a) (hp_certK b) := by
    rw [← hg4_cupH1_mk hg4_sigmaK b4b_root hprod 1 α β]
    change hg4_cupH1 hg4_sigmaK b4b_root 1
      (hg4_shapiroH1 hg4_sigmaK b4b_root (Submodule.Quotient.mk ⟨hp_certK a, hmem a⟩))
      (hg4_shapiroH1 hg4_sigmaK b4b_root (Submodule.Quotient.mk ⟨hp_certK b, hmem b⟩)) = _
    rw [hg4_cupH1_shapiro hg4_sigmaK b4b_root hprod 1 (by simp) hinv,
      pc_SPar_mk _ 1 hprodT (by simp) (fun i => hinv _) _ _ (hmem a) (hmem b)]
  have h4 : (4 : hp_K) ≠ 0 := by
    have : (4 : hp_K) = algebraMap ℚ hp_K 4 := by simp
    rw [this, Ne, map_eq_zero_iff _ (algebraMap ℚ hp_K).injective]
    norm_num
  change (1 + 2 * pc_zeta) * (4 * hg6_coordCup b4b_root 0 0
    (α : hg_Edge b4b_Group 13 → Fin 4 → hp_K) β) = _
  rw [hg6_coordCup_schur _ _ hα hβ 0 0]
  simp only [↓reduceIte]
  rw [mul_inv_cancel_left₀ h4, hcup, ← hgram]
  ring

end HodgeLean.Foundations.Program

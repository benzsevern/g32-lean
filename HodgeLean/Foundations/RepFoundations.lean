import HodgeLean.Foundations.RepFoundationsProofs

/-!
# Representation foundations for finite groups (FROZEN SPEC)

Eight statements about a representation `ρ` of an arbitrary finite group `G` on a
finite-dimensional complex vector space `V`, with simple objects of `FDRep ℂ G`:

1. the isotypic decomposition `⊕_i σ_i ⊗ Hom_G(σ_i, V) ≅ V` for a family `σ` of pairwise
   non-isomorphic simple representations representing every isomorphism class;
2. the determinant of a centralizer element `u` as `∏_i det(u | M_{σ_i})^{dim σ_i}`;
3. the same product on a `χ`-eigenspace of a subgroup, with exponents `dim σ_i^{H, χ}`;
4. the Frobenius–Schur indicator of a simple representation lies in `{1, 0, -1}`, and is `0`
   exactly for a character that is not real-valued;
5. the indicator classifies the invariant bilinear forms (symmetric, alternating, none);
6. `e_σ̄ · e_σ = 1` for `e_σ = det(u | M_σ)` and `u` preserving a nondegenerate invariant form;
7. `e_σ = 1` for `σ` of indicator `1` when that form is alternating;
8. vanishing of `M_σ` when the character inner product is a nonpositive integer.

These are implications from the stated hypotheses about finite-dimensional complex
representations only. Nothing here mentions a variety, cohomology, Hodge classes or
algebraicity, and nothing is specific to `G₃₂`; the adapters to `g32c_mult`, `g32c_U` and the
Chevalley–Weil field are later stages (see `docs/specs/RepFoundations.md`).
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory
open scoped TensorProduct

variable {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/-- **Isotypic decomposition.** For a family of pairwise non-isomorphic simple representations
representing every simple isomorphism class, evaluation `⊕_i σ_i ⊗ Hom_G(σ_i, V) → V` is a
linear isomorphism.
Source: Serre, *Linear representations of finite groups*, §2.6, Theorem 8 (canonical
decomposition) and §2.7; Fulton–Harris, *Representation theory*, §1.2 and Exercise 2.37;
Maschke's theorem (Mathlib `MonoidAlgebra.Submodule.exists_isCompl`) and Schur's lemma
(Mathlib `FDRep.finrank_hom_simple_simple`). -/
theorem rfd_eval_bijective {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i)) :
    Function.Bijective (rfd_eval σ ρ) :=
  rfd_eval_bijective_aux σ ρ hσ hdist hcov

/-- The evaluation map is a linear equivalence. -/
example {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i)) :
    ∃ e : (∀ i, σ i ⊗[ℂ] rfd_mult (σ i) ρ) ≃ₗ[ℂ] V, ⇑e = rfd_eval σ ρ :=
  ⟨LinearEquiv.ofBijective _ (rfd_eval_bijective σ ρ hσ hdist hcov), rfl⟩

/-- **Determinant formula.** A centralizer element `u` acts on `V ≅ ⊕_i σ_i ⊗ M_{σ_i}` as
`⊕_i 1 ⊗ (u ∘ -)`, so `det u = ∏_i det(u | M_{σ_i})^{dim σ_i}`.
Source: Serre, *Linear representations of finite groups*, §2.6; Bourbaki, *Algèbre*, ch. III,
§8, no. 4 (`det(1_a ⊗ B) = det(B)^a`); G32 v0.16, Subsection 4.2. -/
theorem rfd_det_eq_prod {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i))
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    LinearMap.det u = ∏ i, rfd_det (σ i) ρ u hu ^ Module.finrank ℂ (σ i) :=
  rfd_det_eq_prod_aux σ ρ hσ hdist hcov u hu

/-- A centralizer element acting trivially on every multiplicity space has determinant one. -/
example {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i))
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ))
    (h1 : ∀ i, rfd_det (σ i) ρ u hu = 1) :
    LinearMap.det u = 1 := by
  rw [rfd_det_eq_prod σ ρ hσ hdist hcov u hu]
  simp [h1]

/-- **Determinant on an eigenspace of a subgroup.** For `H ≤ G` and `χ : H → ℂˣ`,
`V^{H, χ} ≅ ⊕_i σ_i^{H, χ} ⊗ M_{σ_i}`, so
`det(u | V^{H, χ}) = ∏_i det(u | M_{σ_i})^{dim σ_i^{H, χ}}`.
Source: Serre, *Linear representations of finite groups*, §2.6 and §7.1; G32 v0.16, proof of
Proposition 4.6 (the character of `U` on `det H¹(C, ℂ)^{H′, χ}` is `∏_τ e_τ^{m(τ|H′, χ)}`). -/
theorem rfd_det_eigen {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i))
    (H : Subgroup G) (χ : H →* ℂˣ)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    LinearMap.det (rfd_eigenAct ρ H χ u hu) =
      ∏ i, rfd_det (σ i) ρ u hu ^ Module.finrank ℂ (rfd_eigen (σ i).ρ H χ) :=
  rfd_det_eigen_aux σ ρ hσ hdist hcov H χ u hu

/-- Summands with no `χ`-eigenvector do not contribute. -/
example {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i))
    (H : Subgroup G) (χ : H →* ℂˣ)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ))
    (h0 : ∀ i, rfd_eigen (σ i).ρ H χ = ⊥) :
    LinearMap.det (rfd_eigenAct ρ H χ u hu) = 1 := by
  rw [rfd_det_eigen σ ρ hσ hdist hcov H χ u hu]
  exact Finset.prod_eq_one fun i _ => by rw [h0 i, finrank_bot, pow_zero]

/-- **Frobenius–Schur indicator.** The indicator of a simple representation is `1`, `0` or `-1`,
and it is `0` exactly when the character is not real-valued (`σ` not self-dual).
Source: Serre, *Linear representations of finite groups*, §13.2, Propositions 38 and 39;
Isaacs, *Character theory of finite groups*, Theorem 4.5. -/
theorem rfd_indicator_trichotomy (σ : FDRep ℂ G) (hσ : Simple σ) :
    (rfd_indicator σ = 1 ∨ rfd_indicator σ = 0 ∨ rfd_indicator σ = -1) ∧
      (rfd_indicator σ = 0 ↔ ¬ ∀ g, star (σ.character g) = σ.character g) :=
  rfd_indicator_trichotomy_aux σ hσ

/-- The indicator of a simple representation is never `2`. -/
example (σ : FDRep ℂ G) (hσ : Simple σ) : rfd_indicator σ ≠ 2 := by
  rcases (rfd_indicator_trichotomy σ hσ).1 with h | h | h <;> rw [h] <;> norm_num

/-- A self-dual simple representation that is not of indicator `-1` has indicator `1`: the
orthogonal case of `rfd_det_orthogonal`. -/
example (σ : FDRep ℂ G) (hσ : Simple σ) (hsd : ∀ g, star (σ.character g) = σ.character g)
    (hq : rfd_indicator σ ≠ -1) : rfd_indicator σ = 1 := by
  obtain ⟨h3, h0⟩ := rfd_indicator_trichotomy σ hσ
  rcases h3 with h | h | h
  · exact h
  · exact absurd hsd (h0.1 h)
  · exact absurd h hq

/-- **Frobenius–Schur classification of invariant forms.** For a simple `σ`: indicator `1` iff
there is a nonzero invariant symmetric form, `-1` iff there is a nonzero invariant alternating
form, `0` iff the only invariant bilinear form is zero.
Source: Serre, *Linear representations of finite groups*, §13.2, Proposition 38 and its
proof (`χ_σ(g²) = χ_{Sym²}(g) - χ_{Λ²}(g)`); Fulton–Harris, *Representation theory*,
Exercise 3.38; Isaacs, *Character theory of finite groups*, Theorem 4.5 and Corollary 4.15. -/
theorem rfd_indicator_forms (σ : FDRep ℂ G) (hσ : Simple σ) :
    (rfd_indicator σ = 1 ↔ ∃ B ∈ rfd_invForms σ, B ≠ 0 ∧ B.IsSymm) ∧
    (rfd_indicator σ = -1 ↔ ∃ B ∈ rfd_invForms σ, B ≠ 0 ∧ B.IsAlt) ∧
    (rfd_indicator σ = 0 ↔ rfd_invForms σ = ⊥) :=
  rfd_indicator_forms_aux σ hσ

/-- A simple representation of indicator `-1` carries a nonzero invariant alternating form. -/
example (σ : FDRep ℂ G) (hσ : Simple σ) (h : rfd_indicator σ = -1) :
    ∃ B ∈ rfd_invForms σ, B ≠ 0 ∧ B.IsAlt :=
  (rfd_indicator_forms σ hσ).2.1.1 h

/-- **Dual multiplicity spaces.** If `u` centralizes `ρ(G)` and preserves a nondegenerate
`G`-invariant bilinear form `ω` on `V`, and `σ̄` has the conjugate character of a simple `σ`,
then `ω` restricts to a perfect `u`-invariant pairing of `M_σ` with `M_σ̄`, so
`det(u | M_σ̄) · det(u | M_σ) = 1`. For self-dual `σ` (`σ̄ = σ`) this is `e_σ² = 1`, which
covers quaternionic `σ`.
Source: Serre, *Linear representations of finite groups*, §2.6 and §13.2; G32 v0.16,
Subsection 4.2 (`U(ℂ) = ∏ GL(M_τ) × ∏ O(M_θ) × ∏ Sp(M_σ)`, with `M_τ̄` dual to `M_τ`). -/
theorem rfd_det_mul_dual (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (hω : ω.Nondegenerate) (hωG : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y)
    (σ σbar : FDRep ℂ G) (hσ : Simple σ)
    (hchar : ∀ g, σbar.character g = star (σ.character g))
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ))
    (huω : ∀ x y, ω (u x) (u y) = ω x y) :
    rfd_det σbar ρ u hu * rfd_det σ ρ u hu = 1 :=
  rfd_det_mul_dual_aux ρ ω hω hωG σ σbar hσ hchar u hu huω

/-- Quaternionic parity: for a self-dual simple `θ`, `e_θ² = 1`. -/
example (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (hω : ω.Nondegenerate) (hωG : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y)
    (θ : FDRep ℂ G) (hθ : Simple θ) (hsd : ∀ g, star (θ.character g) = θ.character g)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ))
    (huω : ∀ x y, ω (u x) (u y) = ω x y) :
    rfd_det θ ρ u hu ^ 2 = 1 := by
  rw [sq]
  exact rfd_det_mul_dual ρ ω hω hωG θ θ hθ (fun g => (hsd g).symm) u hu huω

/-- **Orthogonal type.** If `ω` is moreover alternating and `σ` is simple of indicator `1`,
the form induced on `M_σ` is alternating and nondegenerate, so `u` acts on `M_σ` through a
symplectic group and `det(u | M_σ) = 1`.
Source: Serre, *Linear representations of finite groups*, §13.2; Bourbaki, *Algèbre*,
ch. IX, §5, no. 2 (symplectic transformations have determinant one); Mathlib
`Matrix.SymplecticGroup`; G32 v0.16, Subsection 4.2 (factors `Sp(M_σ)`). -/
theorem rfd_det_orthogonal (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (hω : ω.Nondegenerate) (hωalt : ω.IsAlt) (hωG : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y)
    (σ : FDRep ℂ G) (hσ : Simple σ) (hν : rfd_indicator σ = 1)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ))
    (huω : ∀ x y, ω (u x) (u y) = ω x y) :
    rfd_det σ ρ u hu = 1 :=
  rfd_det_orthogonal_aux ρ ω hω hωalt hωG σ hσ hν u hu huω

/-- The character `e_σ` of an orthogonal `σ` is trivial on powers of `u` as well. -/
example (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (hω : ω.Nondegenerate) (hωalt : ω.IsAlt) (hωG : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y)
    (σ : FDRep ℂ G) (hσ : Simple σ) (hν : rfd_indicator σ = 1)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ))
    (huω : ∀ x y, ω (u x) (u y) = ω x y) (k : ℕ) :
    rfd_det σ ρ u hu ^ k = 1 := by
  rw [rfd_det_orthogonal ρ ω hω hωalt hωG σ hσ hν u hu huω, one_pow]

/-- **Vanishing multiplicities.** `dim Hom_G(σ, V) = |G|⁻¹ Σ_g tr ρ(g) · conj χ_σ(g)`, so if
this inner product equals an integer `n ≤ 0` then `M_σ = 0`. With the Chevalley–Weil value
`n = m_σ` this is the vanishing used for the G32 contraction.
Source: Serre, *Linear representations of finite groups*, §2.3, Theorem 3 and §2.6;
Mathlib `FDRep.scalar_product_char_eq_finrank_equivariant`; G32 v0.16, Proposition 3.1. -/
theorem rfd_mult_eq_bot (σ : FDRep ℂ G) (ρ : Representation ℂ G V) (n : ℤ)
    (hn : (Fintype.card G : ℂ)⁻¹ *
      ∑ g, LinearMap.trace ℂ V (ρ g) * star (σ.character g) = n)
    (hle : n ≤ 0) :
    rfd_mult σ ρ = ⊥ :=
  rfd_mult_eq_bot_aux σ ρ n hn hle

/-- With a vanishing multiplicity space, `e_σ = 1`. -/
example (σ : FDRep ℂ G) (ρ : Representation ℂ G V) (n : ℤ)
    (hn : (Fintype.card G : ℂ)⁻¹ *
      ∑ g, LinearMap.trace ℂ V (ρ g) * star (σ.character g) = n)
    (hle : n ≤ 0) (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    rfd_det σ ρ u hu = 1 := by
  have h := rfd_mult_eq_bot σ ρ n hn hle
  have : Subsingleton (rfd_mult σ ρ) := by
    rw [h]
    infer_instance
  exact LinearMap.det_eq_one_of_subsingleton _

end HodgeLean.Foundations

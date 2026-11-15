import HodgeLean.Foundations.Program.PrymParabolicComparisonProofs
import HodgeLean.Foundations.Program.ParabolicCohomology
import HodgeLean.Foundations.Program.PrymVariationCentreChevalleyWeil

/-! # Stage H3a: parabolic cohomology on the lifted Δ-complex of G32 Figure 1 (FROZEN SPEC)

The frozen spec for `docs/briefs/cloud-spec-h3.md` (`docs/specs/PrymParabolicComparison.md`). Do
not edit this file. Each theorem restates the matching `_aux` theorem in
`PrymParabolicComparisonProofs.lean`.

**Claimed (once the bodies are proved).** For a group `G` and a tuple `g` of length `r`, on the
explicit lifted complex `X̃(g)` of `PrymParabolicComparisonDefs`:
- the cellular coboundaries compose to zero when `g₀ ⋯ g_{r−1} = 1`;
- for a generating tuple with `r > 0`, cellular `H⁰` with coefficients in any field is a line;
- for a finite group, a generating tuple and product one, cellular `H¹` satisfies the
  Riemann–Hurwitz count `dim H¹ + 2|G| + Σ_i |G/⟨g_i⟩| = r|G| + 2`, over any field;
- for a representation `σ : G →* Matrix ι ι K` and any tuple, the explicit Shapiro map sends the
  parameter space `pc_Z (pc_tuple σ g)` of stage H2 into the equivariant `1`-cocycles, and a
  parameter goes to an equivariant coboundary exactly when it lies in the trivial part
  `pc_trivialPart`; under product one every equivariant cocycle is the image of a parameter up
  to an equivariant coboundary. Together these give `pc_Vpar (pc_tuple σ g) ≃ H¹_σ(X̃(g))` (first chain check);
- for a finite group whose order is invertible in `K`, an equivariant `1`-cochain that is the
  coboundary of some `0`-cochain is the coboundary of an equivariant one;
- the orientation chain `Σ_x Σ_i (A_i(x) − B_i(x))` is a cycle: every coboundary vanishes on it;
- for a finite group and a Hermitian form `H` invariant under `σ`, the cellular cup product of the
  Shapiro images of `a` and `b`, evaluated on that cycle, is `−|G|·conj S(b, a)`, with `S` the
  cup-product formula `pc_S` of G32 Lemma 6.2; on `Z` this is `|G|·S(a, b)`.

The chain checks give, for the G32 root `b4b_root` on `ℂ⁴`: `dim H¹_σ(X̃) = 6`, and Gram matrix
`|G|·g32H0 ω` for `(1 + 2ω)` times the cellular cup product in the basis of Shapiro images of the
H6 certificate (scale `|G| > 0`).

**Not claimed.** That the realization of `X̃(g)` is homeomorphic to a compact marked cover `C_t` of
B6-2; that cellular and singular (co)homology agree; that `H¹_σ(X̃)` is the `σ`-part of the
B6-3 Prym lattice or that the evaluation on the orientation cycle is the B3 intersection form;
the Prym comparison on the saturated rational lattice (H5); any fibre discriminant (H7). The
statements are an implication from the stated combinatorial and algebraic hypotheses only. The
tuple of the chain checks is the repository's `b4b_root`; nothing here identifies it with the
monodromy of the paper's base point `C₀`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

/-! ## The cellular complex -/

/-- **The lifted complex is a cochain complex** when `g₀ ⋯ g_{r−1} = 1`: `δ¹ ∘ δ⁰ = 0`, for any
coefficient module. The only triangle where product one enters is `B_{r−1}`, whose faces
`h_{r−1}` and `f₀` end at `b_∞(x (g₀ ⋯ g_{r−1})⁻¹)` and `b_∞(x)`.
Source: G32 v0.16, Figure 1 and §3.1 (the product relation of a Nielsen tuple); Hatcher,
*Algebraic Topology*, §2.1. -/
theorem hg_delta_comp {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (hprod : (List.ofFn g).prod = 1) :
    hg_delta1 R M g ∘ₗ hg_delta0 R M g = 0 :=
  hg_delta_comp_aux g hprod

example {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (hprod : (List.ofFn g).prod = 1) :
    hg_delta1 R M g ∘ₗ hg_delta0 R M g = 0 :=
  hg_delta_comp g hprod

/-- **The lifted complex is connected** for a generating tuple with `r > 0`: the locally constant
`0`-cochains with values in a field form a line.
Source: Hatcher, §1.3 (a covering of a connected space is connected iff the monodromy is
transitive) and §2.1 (`H₀` of a connected complex); G32 v0.16, §3.1. -/
theorem hg_H0_finrank (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (hr : 0 < r) (hg : Subgroup.closure (Set.range g) = ⊤) :
    Module.finrank K (LinearMap.ker (hg_delta0 K K g)) = 1 :=
  hg_H0_finrank_aux K g hr hg

example (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (hr : 0 < r) (hg : Subgroup.closure (Set.range g) = ⊤) :
    Module.finrank K (LinearMap.ker (hg_delta0 K K g)) = 1 :=
  hg_H0_finrank K g hr hg

/-- **Riemann–Hurwitz for the lifted complex.** For a finite group, a generating tuple with
product one and any field: `dim H¹ + 2|G| + Σ_i |G/⟨g_i⟩| = r|G| + 2`. The complex has
`2|G| + Σ_i |G/⟨g_i⟩|` vertices, `3r|G|` edges and `2r|G|` triangles, and it is a connected
compact oriented surface without boundary, so `dim H⁰ = dim H² = 1`.
Source: Hatcher, §2.2 (Euler characteristic) and §3.3 (`H²` of a compact connected orientable
surface); Riemann–Hurwitz, Forster, *Lectures on Riemann Surfaces*, Theorem 17.14. -/
theorem hg_H1_finrank (K : Type*) [Field K] {G : Type*} [Group G] [Finite G] {r : ℕ}
    (g : Fin r → G) (hprod : (List.ofFn g).prod = 1)
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    (Module.finrank K (hg_H1 K g) : ℤ) + 2 * Nat.card G +
        ∑ i, (Nat.card (G ⧸ Subgroup.zpowers (g i)) : ℤ) =
      r * Nat.card G + 2 :=
  hg_H1_finrank_aux K g hprod hg

example (K : Type*) [Field K] {G : Type*} [Group G] [Finite G] {r : ℕ}
    (g : Fin r → G) (hprod : (List.ofFn g).prod = 1)
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    (Module.finrank K (hg_H1 K g) : ℤ) + 2 * Nat.card G +
        ∑ i, (Nat.card (G ⧸ Subgroup.zpowers (g i)) : ℤ) =
      r * Nat.card G + 2 :=
  hg_H1_finrank K g hprod hg

/-! ## Shapiro's lemma on the explicit complex -/

/-- **Parameters give equivariant cocycles.** For any tuple and `a ∈ Z`, the Shapiro image of `a`
is a cocycle. On `A_i` the relation `h = f − e` holds by construction; on `B_i` it is the
recursion `F_{i+1} = F_i + Q_i c_i`, and on `B_{r−1}` it is `Σ_i Q_i c_i = 0`.
Source: G32 v0.16, Lemma 6.2 (parabolic cocycles and their parameters); Brown, *Cohomology of
Groups*, Chapter III, §5. -/
theorem hg_shapiro_cocycle {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (a : Fin r → ι → K) (ha : a ∈ pc_Z (pc_tuple σ g)) :
    hg_shapiroCochain σ g a ∈ LinearMap.ker (hg_delta1 K (ι → K) g) :=
  hg_shapiro_cocycle_aux σ g a ha

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (a : Fin r → ι → K) (ha : a ∈ pc_Z (pc_tuple σ g)) :
    hg_shapiroCochain σ g a ∈ LinearMap.ker (hg_delta1 K (ι → K) g) :=
  hg_shapiro_cocycle σ g a ha

/-- **Coboundaries correspond to the trivial part.** For any tuple and any parameter `a`, the
Shapiro image of `a` is the coboundary of an equivariant `0`-cochain if and only if `a` is a
constant tuple plus a tuple in `Π_i ker(T_i − 1)`.
Source: G32 v0.16, Lemma 6.2 and proof of Proposition 6.3 (the radical is spanned by
coboundaries and the tuples with `a_i ∈ ker(1 − T_i)`); Brown, Chapter III, §5. -/
theorem hg_shapiro_coboundary_iff {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (a : Fin r → ι → K) :
    hg_shapiroCochain σ g a ∈ hg_eqCoboundaries σ g ↔ a ∈ pc_trivialPart (pc_tuple σ g) :=
  hg_shapiro_coboundary_iff_aux σ g a

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (a : Fin r → ι → K) :
    hg_shapiroCochain σ g a ∈ hg_eqCoboundaries σ g ↔ a ∈ pc_trivialPart (pc_tuple σ g) :=
  hg_shapiro_coboundary_iff σ g a

/-- **Every equivariant cocycle comes from a parameter**, up to an equivariant coboundary, when
`g₀ ⋯ g_{r−1} = 1`. Subtract the coboundary of the `0`-cochain `b_∞(y) ↦ σ(y) c(f₀(1))`; the
values on the `e_i(1)` are then the parameters.
Source: G32 v0.16, Lemma 6.2; Brown, Chapter III, §5 (Shapiro's lemma). -/
theorem hg_shapiro_surjective {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (c : hg_Edge G r → ι → K) (hc : c ∈ hg_eqCocycles σ g) :
    ∃ a ∈ pc_Z (pc_tuple σ g), c - hg_shapiroCochain σ g a ∈ hg_eqCoboundaries σ g :=
  hg_shapiro_surjective_aux σ g hprod c hc

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (c : hg_Edge G r → ι → K) (hc : c ∈ hg_eqCocycles σ g) :
    ∃ a ∈ pc_Z (pc_tuple σ g), c - hg_shapiroCochain σ g a ∈ hg_eqCoboundaries σ g :=
  hg_shapiro_surjective σ g hprod c hc

/-- **Equivariant classes are invariant classes** when `|G|` is invertible in `K`: an equivariant
`1`-cochain that is the coboundary of some `0`-cochain `φ` is the coboundary of the equivariant
average `|G|⁻¹ Σ_h σ(h) φ(h⁻¹ ·)`. So `H¹_σ(X̃)` injects into `H¹(X̃; V)`.
Source: Serre, *Linear Representations of Finite Groups*, §2.6 (averaging over `G`); Brown,
Chapter III, §10 (`H^n(G, M) = 0` for `n > 0` when `|G|` is invertible on `M`). -/
theorem hg_eqCoboundary_average {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hG : (Fintype.card G : K) ≠ 0) (c : hg_Edge G r → ι → K) (hc : c ∈ hg_eqCochain1 σ)
    (hcb : c ∈ LinearMap.range (hg_delta0 K (ι → K) g)) :
    c ∈ hg_eqCoboundaries σ g :=
  hg_eqCoboundary_average_aux σ g hG c hc hcb

example {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hG : (Fintype.card G : K) ≠ 0) (c : hg_Edge G r → ι → K) (hc : c ∈ hg_eqCochain1 σ)
    (hcb : c ∈ LinearMap.range (hg_delta0 K (ι → K) g)) :
    c ∈ hg_eqCoboundaries σ g :=
  hg_eqCoboundary_average σ g hG c hc hcb

/-! ## The orientation cycle and the cup product -/

/-- **The orientation chain is a cycle**: every coboundary of a `1`-cochain vanishes on
`Σ_x Σ_i (A_i(x) − B_i(x))`, for any tuple and any coefficient module. The `e_i` cancel within
each pair, the `h_i` after reindexing `x ↦ x g_i⁻¹`, and the `f_i` around the cyclic order.
Source: Hatcher, §2.1 and §3.3 (a compact oriented surface without boundary has a fundamental
cycle); G32 v0.16, Figure 1. -/
theorem hg_fundEval_delta1 {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {G : Type*} [Group G] [Fintype G] {r : ℕ} (g : Fin r → G)
    (c : hg_Edge G r → M) :
    hg_fundEval (hg_delta1 R M g c) = 0 :=
  hg_fundEval_delta1_aux g c

example {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {G : Type*} [Group G] [Fintype G] {r : ℕ} (g : Fin r → G)
    (c : hg_Edge G r → M) :
    hg_fundEval (hg_delta1 R M g c) = 0 :=
  hg_fundEval_delta1 (R := R) g c

/-- **The cellular cup product of Shapiro images is the cup-product formula.** For a finite group
and a Hermitian form `H` invariant under `σ`, for all parameters `a, b`:
`⟨Φa ∪ Φb, Σ_x Σ_i (A_i(x) − B_i(x))⟩ = −|G|·conj S(b, a)`. Each sheet contributes
`−Σ_i h(c^a_i, Q_i⁻¹ F^b_i + b_i)`.
Source: G32 v0.16, proof of Lemma 6.2 (the triangle computation); Hatcher, §3.2 (cup product
on a Δ-complex). -/
theorem hg_cup_shapiro {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (H : Matrix ι ι K) (hHerm : Hᴴ = H) (hinv : ∀ x, (σ x)ᴴ * H * σ x = H)
    (a b : Fin r → ι → K) :
    hg_fundEval (hg_cup g H (hg_shapiroCochain σ g a) (hg_shapiroCochain σ g b)) =
      -((Fintype.card G : K) * star (pc_S (pc_tuple σ g) H b a)) :=
  hg_cup_shapiro_aux σ g H hHerm hinv a b

example {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (H : Matrix ι ι K) (hHerm : Hᴴ = H) (hinv : ∀ x, (σ x)ᴴ * H * σ x = H)
    (a b : Fin r → ι → K) :
    hg_fundEval (hg_cup g H (hg_shapiroCochain σ g a) (hg_shapiroCochain σ g b)) =
      -((Fintype.card G : K) * star (pc_S (pc_tuple σ g) H b a)) :=
  hg_cup_shapiro σ g H hHerm hinv a b

/-! ## Satisfiable instances -/

/-- The sign character of `ℤˣ = {±1}` on `ℚ¹`. -/
private def hg_signRep : ℤˣ →* Matrix (Fin 1) (Fin 1) ℚ :=
  (Matrix.scalar (Fin 1) : ℚ →+* Matrix (Fin 1) (Fin 1) ℚ).toMonoidHom.comp
    ((Int.castRingHom ℚ).toMonoidHom.comp (Units.coeHom ℤ))

private theorem hg_signRep_neg_one : hg_signRep (-1) = -1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [hg_signRep]

private theorem hg_zpowers_neg_one : Subgroup.zpowers (-1 : ℤˣ) = ⊤ := by
  refine eq_top_iff.2 fun u _ => ?_
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact one_mem _
  · exact Subgroup.mem_zpowers _

/-- A nondegenerate instance (elliptic double cover of the sphere branched at four points):
`G = ℤˣ` of order two, the tuple `(−1, −1, −1, −1)` with product one, generating `G`, the sign
character with the invariant Hermitian form `1`, and `|G| = 2` invertible in `ℚ`. The hypotheses
of every statement hold, and the group, the representation and the tuple are not trivial. -/
example :
    (List.ofFn fun _ : Fin 4 => (-1 : ℤˣ)).prod = 1 ∧
      Subgroup.closure (Set.range fun _ : Fin 4 => (-1 : ℤˣ)) = ⊤ ∧
      Fintype.card ℤˣ = 2 ∧ ((Fintype.card ℤˣ : ℚ) ≠ 0) ∧
      (1 : Matrix (Fin 1) (Fin 1) ℚ)ᴴ = 1 ∧
      (∀ x, (hg_signRep x)ᴴ * 1 * hg_signRep x = 1) ∧
      hg_signRep (-1) ≠ 1 := by
  refine ⟨by simp [List.ofFn_succ], ?_, Fintype.card_units_int, by simp [Fintype.card_units_int],
    by simp, fun x => ?_, ?_⟩
  · rw [eq_top_iff, ← hg_zpowers_neg_one, Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_mono (by rintro _ rfl; exact ⟨0, rfl⟩)
  · rcases Int.units_eq_one_or x with rfl | rfl
    · simp
    · rw [hg_signRep_neg_one]
      simp
  · rw [hg_signRep_neg_one]
    intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this

/-- The instance has nonzero rank: the elliptic double cover has `dim H¹ = 2` by Riemann–Hurwitz
(`hg_H1_finrank`, `|G| = 2`, one point over each branch point). -/
example : Module.finrank ℚ (hg_H1 ℚ fun _ : Fin 4 => (-1 : ℤˣ)) = 2 := by
  have hgen : Subgroup.closure (Set.range fun _ : Fin 4 => (-1 : ℤˣ)) = ⊤ := by
    rw [eq_top_iff, ← hg_zpowers_neg_one, Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_mono (by rintro _ rfl; exact ⟨0, rfl⟩)
  have h := hg_H1_finrank ℚ (fun _ : Fin 4 => (-1 : ℤˣ)) (by simp [List.ofFn_succ]) hgen
  have hq : Nat.card (ℤˣ ⧸ Subgroup.zpowers (-1 : ℤˣ)) = 1 := by
    rw [hg_zpowers_neg_one]
    exact Subgroup.index_top
  simp only [hq, Nat.card_eq_fintype_card, Fintype.card_units_int] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  push_cast at h
  omega

/-- The G32 root satisfies the hypotheses of the cellular statements: thirteen entries, product
one (`b63d_root_product`) and generation (`b63d_root_subgroup`); the defining representation
preserves the standard form (`b63l_toMatrix_mem_unitary`), and `|G|` is invertible in `ℂ`. -/
example :
    0 < 13 ∧ (List.ofFn b4b_root).prod = 1 ∧ Subgroup.closure (Set.range b4b_root) = ⊤ ∧
      (∀ x, (b4b_toMatrix x)ᴴ * 1 * b4b_toMatrix x = 1) ∧
      (Fintype.card b4b_Group : ℂ) ≠ 0 := by
  refine ⟨by norm_num, b63d_root_product, b63d_root_subgroup, fun x => ?_, ?_⟩
  · rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp (b63l_toMatrix_mem_unitary _)
  · exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

/-! ## Chain checks -/

/-- Chain check (Shapiro's lemma on the explicit complex): under product one, the parameter model
of stage H2 is linearly equivalent to the equivariant cellular cohomology of the lifted complex,
through the classes of the Shapiro images. Built from `hg_shapiro_cocycle`,
`hg_shapiro_coboundary_iff` and `hg_shapiro_surjective`. -/
example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) (hprod : (List.ofFn g).prod = 1) :
    ∃ e : pc_Vpar (pc_tuple σ g) ≃ₗ[K] hg_eqH1 σ g,
      ∀ (a : Fin r → ι → K) (ha : a ∈ pc_Z (pc_tuple σ g))
        (hc : hg_shapiroCochain σ g a ∈ hg_eqCocycles σ g),
        e (Submodule.Quotient.mk ⟨a, ha⟩) = Submodule.Quotient.mk ⟨_, hc⟩ := by
  have hmem : ∀ a : pc_Z (pc_tuple σ g),
      hg_shapiroCochain σ g ((pc_Z (pc_tuple σ g)).subtype a) ∈ hg_eqCocycles σ g := by
    intro a
    refine ⟨fun h ε => ?_, hg_shapiro_cocycle σ g a a.2⟩
    rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
      simp [hg_shapiroCochain, hg_actEdge, map_mul, Matrix.mulVec_mulVec, Matrix.mulVec_neg,
        Matrix.mul_assoc]
  let φ : pc_Z (pc_tuple σ g) →ₗ[K] hg_eqCocycles σ g :=
    LinearMap.codRestrict (hg_eqCocycles σ g)
      (hg_shapiroCochain σ g ∘ₗ (pc_Z (pc_tuple σ g)).subtype) hmem
  let ψ : pc_Z (pc_tuple σ g) →ₗ[K] hg_eqH1 σ g := Submodule.mkQ _ ∘ₗ φ
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, ha, hca⟩ := hg_shapiro_surjective σ g hprod c c.2
    refine ⟨⟨a, ha⟩, ?_⟩
    change Submodule.Quotient.mk (φ ⟨a, ha⟩) = Submodule.Quotient.mk c
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    have : (hg_eqCocycles σ g).subtype (φ ⟨a, ha⟩ - c) =
        -(c.1 - hg_shapiroCochain σ g a) := by
      simp [φ]
    rw [this]
    exact Submodule.neg_mem _ hca
  have hker : LinearMap.ker ψ =
      (pc_trivialPart (pc_tuple σ g)).comap (pc_Z (pc_tuple σ g)).subtype := by
    ext a
    simp only [ψ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hg_shapiro_coboundary_iff σ g a
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hsurj),
    fun _ _ _ => rfl⟩

/-- Chain check toward `hpol`: for the G32 root on `ℂ⁴`, the equivariant cellular cohomology of
the explicit lifted complex has dimension six, from the Shapiro statements and `hp_vpar_finrank`. -/
example : Module.finrank ℂ (hg_eqH1 b4b_toMatrix b4b_root) = 6 := by
  have hmem : ∀ a : pc_Z (pc_tuple b4b_toMatrix b4b_root),
      hg_shapiroCochain b4b_toMatrix b4b_root ((pc_Z (pc_tuple b4b_toMatrix b4b_root)).subtype a)
        ∈ hg_eqCocycles b4b_toMatrix b4b_root := by
    intro a
    refine ⟨fun h ε => ?_, hg_shapiro_cocycle b4b_toMatrix b4b_root a a.2⟩
    rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
      simp [hg_shapiroCochain, hg_actEdge, map_mul, Matrix.mulVec_mulVec, Matrix.mulVec_neg,
        Matrix.mul_assoc]
  let φ := LinearMap.codRestrict (hg_eqCocycles b4b_toMatrix b4b_root)
      (hg_shapiroCochain b4b_toMatrix b4b_root ∘ₗ
        (pc_Z (pc_tuple b4b_toMatrix b4b_root)).subtype) hmem
  let ψ : pc_Z (pc_tuple b4b_toMatrix b4b_root) →ₗ[ℂ] hg_eqH1 b4b_toMatrix b4b_root :=
    Submodule.mkQ _ ∘ₗ φ
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, ha, hca⟩ :=
      hg_shapiro_surjective b4b_toMatrix b4b_root b63d_root_product c c.2
    refine ⟨⟨a, ha⟩, ?_⟩
    change Submodule.Quotient.mk (φ ⟨a, ha⟩) = Submodule.Quotient.mk c
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    have : (hg_eqCocycles b4b_toMatrix b4b_root).subtype (φ ⟨a, ha⟩ - c) =
        -(c.1 - hg_shapiroCochain b4b_toMatrix b4b_root a) := by
      simp [φ]
    rw [this]
    exact Submodule.neg_mem _ hca
  have hker : LinearMap.ker ψ = (pc_trivialPart (pc_tuple b4b_toMatrix b4b_root)).comap
      (pc_Z (pc_tuple b4b_toMatrix b4b_root)).subtype := by
    ext a
    simp only [ψ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hg_shapiro_coboundary_iff b4b_toMatrix b4b_root a
  have e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hsurj)
  rw [← e.finrank_eq]
  exact hp_vpar_finrank

/-- Chain check toward `hpol` (the Gram shape of `g32d_ParabolicPolarization`, with a positive
rational scale): on the explicit lifted complex of the G32 root, `(1 + 2ω)` times the cellular cup
product of the Shapiro images of the six H6 certificate tuples, evaluated on the orientation
cycle, has Gram matrix `|G|·g32H0 ω`. From `hg_cup_shapiro`, `pc_S_skew` and `hp_cert_gram`.
Transporting this to the Prym lattice of a fibre is the rest of H3 and stages H4–H5. -/
example (a b : Fin 6) :
    (1 + 2 * HodgeLean.Papers.g32h_omega) *
        hg_fundEval (hg_cup b4b_root 1 (hg_shapiroCochain b4b_toMatrix b4b_root (hp_cert a))
          (hg_shapiroCochain b4b_toMatrix b4b_root (hp_cert b))) =
      (Fintype.card b4b_Group : ℂ) *
        HodgeLean.Papers.g32H0 HodgeLean.Papers.g32h_omega a b := by
  have hinvG : ∀ x, (b4b_toMatrix x)ᴴ * 1 * b4b_toMatrix x = 1 := fun x => by
    rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp (b63l_toMatrix_mem_unitary _)
  have hprodT : (List.ofFn hp_rootTuple).prod = 1 := by
    have hmapC : List.ofFn hp_rootTuple = (List.ofFn b4b_root).map b4b_toMatrix := by
      rw [List.map_ofFn]
      rfl
    rw [hmapC, ← map_list_prod, b63d_root_product, map_one]
  have hskew := pc_S_skew hp_rootTuple 1 hprodT (by simp) (fun j => hinvG (b4b_root j))
    (hp_cert a) (hp_cert b) (hp_cert_mem a) (hp_cert_mem b)
  have hcup := hg_cup_shapiro b4b_toMatrix b4b_root 1 (by simp) hinvG (hp_cert a) (hp_cert b)
  rw [hcup, ← hp_cert_gram a b]
  change _ * -(_ * star (pc_S hp_rootTuple 1 (hp_cert b) (hp_cert a))) = _
  rw [eq_neg_of_add_eq_zero_right hskew]
  ring

end HodgeLean.Foundations.Program

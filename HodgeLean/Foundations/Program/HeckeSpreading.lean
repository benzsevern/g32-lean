import HodgeLean.Foundations.Program.HeckeSpreadingProofs
import HodgeLean.Papers.G32AssemblyDefs

/-! # Hecke spreading S1–S6 for the concrete universal family (FROZEN SPEC)

Stages S1–S6 of `docs/specs/G32RemainingPremises.md`, §2.3, with the corrections of its
review section. Each theorem restates the matching `_aux` theorem in
`HeckeSpreadingProofs.lean`.

What is claimed:
* S1: the Cayley map `X ↦ (1 - X)(1 + X)⁻¹` exchanges the Lie algebra and the group of a
  Gram matrix away from `det(1 + ·) = 0`, is its own inverse there in characteristic zero,
  preserves commutation, and commutes with ring maps;
* S2: rational points of `U(b60_H)`, as `12 × 12` matrices commuting with `ω` and preserving
  `b60_E`, are dense in the real points;
* S3, S4: the real points act transitively on the filtrations `b60_F τ`, every real point moves
  every `τ` to some `σ`, and for fixed `τ` the set of real points moving `τ` into an open set is
  open;
* S5: a rational point moving `τ` to `σ` gives a `K`-linear polarized isogeny
  `b60b_univ τ → b60b_univ σ`;
* S6: the implication from Weil algebraicity of `b60b_univ` on a nonempty open set to Weil
  algebraicity at every point of `g32m_Domain`.

What is not claimed: anything about an abstract `g32m_UniversalFamily` other than one with
`F.univ = b60b_univ`; the existence of an open set of algebraic fibres; the reverse direction
of isogeny transport, or the existence of quasi-inverse isogenies. Stage S7, which turns S6
into the field `spread` of `g32a_premises`, needs a transport input in the direction from
source to target and is not frozen here. HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Matrix TensorProduct
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## S1: the Cayley map -/

/-- **S1a.** The Cayley image of a Lie algebra element with `det(1 + X) ≠ 0` lies in the
unitary group.
Source: Weyl, *The Classical Groups*, Chapter II, §10; plan `G32RemainingPremises.md`, §2.3,
stage S1 (`X*H = -HX` and the commutation of `1 - X` with `1 + X` give `g*Hg = H`). -/
theorem hk_cayley_mem_unitary {K : Type*} [Field K] [StarRing K] {H X : Matrix n n K}
    (hX : X ∈ hk_lie H) (hdet : (1 + X).det ≠ 0) :
    hk_cayley X ∈ hk_unitary H :=
  hk_cayley_mem_unitary_aux hX hdet

example {K : Type*} [Field K] [StarRing K] {H X : Matrix n n K}
    (hX : X ∈ hk_lie H) (hdet : (1 + X).det ≠ 0) :
    (hk_cayley X)ᴴ * H * hk_cayley X = H :=
  hk_cayley_mem_unitary hX hdet

/-- **S1b.** The Cayley image of a group element with `det(1 + g) ≠ 0` lies in the Lie
algebra.
Source: Weyl, *The Classical Groups*, Chapter II, §10; plan `G32RemainingPremises.md`, §2.3,
stage S1. -/
theorem hk_cayley_mem_lie {K : Type*} [Field K] [StarRing K] {H g : Matrix n n K}
    (hg : g ∈ hk_unitary H) (hdet : (1 + g).det ≠ 0) :
    hk_cayley g ∈ hk_lie H :=
  hk_cayley_mem_lie_aux hg hdet

example {K : Type*} [Field K] [StarRing K] {H g : Matrix n n K}
    (hg : g ∈ hk_unitary H) (hdet : (1 + g).det ≠ 0) :
    (hk_cayley g)ᴴ * H + H * hk_cayley g = 0 :=
  hk_cayley_mem_lie hg hdet

/-- **S1c.** In characteristic zero the Cayley map preserves `det(1 + ·) ≠ 0`, since
`1 + (1 - X)(1 + X)⁻¹ = 2(1 + X)⁻¹`.
Source: Weyl, *The Classical Groups*, Chapter II, §10; review `hlean-rev-hps`, S1
(`[CharZero K]`). -/
theorem hk_cayley_det {K : Type*} [Field K] [CharZero K] {X : Matrix n n K}
    (hdet : (1 + X).det ≠ 0) :
    (1 + hk_cayley X).det ≠ 0 :=
  hk_cayley_det_aux hdet

example {K : Type*} [Field K] [CharZero K] {X : Matrix n n K}
    (hdet : (1 + X).det ≠ 0) :
    (1 + hk_cayley X).det ≠ 0 :=
  hk_cayley_det hdet

/-- **S1d.** In characteristic zero the Cayley map is its own inverse on `det(1 + X) ≠ 0`.
Source: Weyl, *The Classical Groups*, Chapter II, §10; review `hlean-rev-hps`, S1. -/
theorem hk_cayley_cayley {K : Type*} [Field K] [CharZero K] {X : Matrix n n K}
    (hdet : (1 + X).det ≠ 0) :
    hk_cayley (hk_cayley X) = X :=
  hk_cayley_cayley_aux hdet

example {K : Type*} [Field K] [CharZero K] {X : Matrix n n K}
    (hdet : (1 + X).det ≠ 0) :
    hk_cayley (hk_cayley X) = X :=
  hk_cayley_cayley hdet

/-- **S1e.** The Cayley map preserves commutation with a fixed matrix.
Source: Weyl, *The Classical Groups*, Chapter II, §10 (the Cayley image is a rational function
of `X`). -/
theorem hk_cayley_commute {K : Type*} [Field K] {X Ω : Matrix n n K}
    (h : X * Ω = Ω * X) :
    hk_cayley X * Ω = Ω * hk_cayley X :=
  hk_cayley_commute_aux h

example {K : Type*} [Field K] {X Ω : Matrix n n K}
    (h : X * Ω = Ω * X) :
    hk_cayley X * Ω = Ω * hk_cayley X :=
  hk_cayley_commute h

/-- **S1f.** The Cayley map commutes with every ring map between fields, in particular with
`ℚ → ℝ` and `ℚ(√-3) → ℂ`.
Source: Mathlib `Matrix.nonsing_inv` (adjugate formula); a ring map between fields is
injective. -/
theorem hk_cayley_map {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (X : Matrix n n K) :
    (hk_cayley X).map f = hk_cayley (X.map f) :=
  hk_cayley_map_aux f X

example (X : Matrix n n ℚ) :
    (hk_cayley X).map (Rat.castHom ℝ) = hk_cayley (X.map (Rat.castHom ℝ)) :=
  hk_cayley_map (Rat.castHom ℝ) X

/-- A nonzero instance of every hypothesis of S1a: a rotation generator in `𝔲(1)` over `ℚ`. -/
example : hk_cayley !![(0 : ℚ), 1; -1, 0] ∈ hk_unitary (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  apply hk_cayley_mem_unitary
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · simp [Matrix.det_fin_two]

/-! ## S2: density of rational points -/

/-- **S2a.** The rational Lie algebra is dense in the real Lie algebra: both are cut out by
the same linear equations with rational coefficients.
Source: Bourbaki, *Algèbre*, Ch. II, §8 (a `ℚ`-form of a subspace defined over `ℚ`); plan
`G32RemainingPremises.md`, §2.3, stage S2. -/
theorem hk_lieAlg_dense {X : Matrix hk_ι hk_ι ℝ} (hX : X ∈ hk_lieAlg ℝ) :
    X ∈ closure (hk_ratCast '' hk_lieAlg ℚ) :=
  hk_lieAlg_dense_aux hX

example {X : Matrix hk_ι hk_ι ℝ} (hX : X ∈ hk_lieAlg ℝ) :
    X ∈ closure (hk_ratCast '' hk_lieAlg ℚ) :=
  hk_lieAlg_dense hX

/-- **S2b.** On the Cayley chart `det(1 + g) ≠ 0`, rational points of the group are dense in
the real points.
Source: plan `G32RemainingPremises.md`, §2.3, stage S2; S1 and S2a with the continuity of the
Cayley map on `det(1 + X) ≠ 0`. -/
theorem hk_chart_dense {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ)
    (hdet : (1 + g).det ≠ 0) :
    g ∈ closure (hk_ratCast '' hk_group ℚ) :=
  hk_chart_dense_aux hg hdet

example : (1 : Matrix hk_ι hk_ι ℝ) ∈ closure (hk_ratCast '' hk_group ℚ) :=
  hk_chart_dense (by simp [hk_group, hk_unitary]) (by
    rw [show (1 : Matrix hk_ι hk_ι ℝ) + 1 = (2 : ℝ) • 1 by rw [two_smul]]
    simp)

/-- **S2.** Rational points of `U(b60_H)` are dense in its real points `U(3,3)`. A general `g`
is `(λ̄·1)(λg)` with both factors in the Cayley chart, for a unit scalar `λ` of `K ⊗ ℝ`.
Source: plan `G32RemainingPremises.md`, §2.3, stage S2 (S2b on both factors, with the
continuity of matrix multiplication). -/
theorem hk_rational_dense {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) :
    g ∈ closure (hk_ratCast '' hk_group ℚ) :=
  hk_rational_dense_aux hg

/-- `-1` is outside the Cayley chart, so S2 covers it while S2b does not. -/
example : (-1 : Matrix hk_ι hk_ι ℝ) ∈ closure (hk_ratCast '' hk_group ℚ) :=
  hk_rational_dense (by simp [hk_group, hk_unitary])

/-! ## S3, S4: the action on the bounded domain -/

/-- **S3.** The real points act transitively on the filtrations `b60_F τ`.
Source: plan `G32RemainingPremises.md`, §2.3, stage S3 (Gram–Schmidt on positive 3-planes
and their orthogonal complements); `b60c_fixed_filtration_chart`. -/
theorem hk_transitive (τ σ : g32m_Domain) :
    ∃ g ∈ hk_group ℝ, hk_moves g τ σ :=
  hk_transitive_aux τ σ

example (τ σ : g32m_Domain) :
    ∃ g ∈ hk_group ℝ, b60_F σ = (b60_F τ).map (hk_toC g) :=
  hk_transitive τ σ

/-- **S4a.** Every real point moves every domain point to a domain point. Uniqueness of the
image is `b60_F_injective`.
Source: plan `G32RemainingPremises.md`, §2.3, stage S4; `b60c_fixed_filtration_chart` (the
image filtration satisfies its hypotheses). -/
theorem hk_action_exists {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ)
    (τ : g32m_Domain) :
    ∃ σ, hk_moves g τ σ :=
  hk_action_exists_aux hg τ

example {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) (τ : g32m_Domain) :
    ∃! σ, hk_moves g τ σ := by
  obtain ⟨σ, hσ⟩ := hk_action_exists hg τ
  refine ⟨σ, hσ, fun σ' hσ' => ?_⟩
  apply Subtype.ext
  exact b60_F_injective (hσ'.trans hσ.symm)

/-- **S4b.** For fixed `τ`, the real points moving `τ` into an open set form an open set:
the coordinate of `g · τ` is a rational function of the entries of `g` with nonvanishing
denominator.
Source: plan `G32RemainingPremises.md`, §2.3, stage S4; review `hlean-rev-hps` (the
every-point argument). -/
theorem hk_moves_open (τ : g32m_Domain) {U : Set g32m_Domain} (hU : IsOpen U) :
    IsOpen {g : hk_group ℝ | ∃ σ ∈ U, hk_moves g.1 τ σ} :=
  hk_moves_open_aux τ hU

example (τ : g32m_Domain) :
    IsOpen {g : hk_group ℝ | ∃ σ ∈ (Set.univ : Set g32m_Domain), hk_moves g.1 τ σ} :=
  hk_moves_open τ isOpen_univ

/-! ## S5, S6: Hecke isogenies and propagation -/

/-- **S5.** A rational point moving `τ` to `σ` gives a `K`-linear polarized isogeny between
the fibres, after clearing denominators.
Source: plan `G32RemainingPremises.md`, §2.3, stage S5; `b60c_uniformization` with the
marking `b60c_fibreMarking`; Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2. -/
theorem hk_hecke_isog {g : Matrix hk_ι hk_ι ℚ} (hg : g ∈ hk_group ℚ)
    {τ σ : g32m_Domain} (h : hk_moves (hk_ratCast g) τ σ) :
    g32t_KIsog (b60b_univ τ) (b60b_univ σ) :=
  hk_hecke_isog_aux hg h

example (τ : g32m_Domain) : g32t_KIsog (b60b_univ τ) (b60b_univ τ) :=
  hk_hecke_isog (g := 1) (by simp [hk_group, hk_unitary])
    (by simp [hk_moves, hk_ratCast, hk_toC, Matrix.toLin_one])

/-- **S6.** The implication from Weil algebraicity of the concrete family on a nonempty open
set to Weil algebraicity at every point. For fixed `τ`, `{g | g · τ ∈ U}` is open (S4b) and
nonempty (S3), so it contains a rational `g` (S2); S5 and `g32tr_weilAlg_pullback` move
algebraicity from `g · τ` to `τ`.
Source: plan `G32RemainingPremises.md`, §2.3, stage S6, with review `hlean-rev-hps`;
G32 v0.16, Lemma 2.2 (pullback direction). -/
theorem hk_weilAlg_of_open {U : Set g32m_Domain} (hU : IsOpen U) (hne : U.Nonempty)
    (hAlg : ∀ m ∈ U, g32t_WeilAlg (b60b_univ m)) (τ : g32m_Domain) :
    g32t_WeilAlg (b60b_univ τ) :=
  hk_weilAlg_of_open_aux hU hne hAlg τ

/-- The hypotheses on `U` are satisfiable: the origin lies in the domain. -/
example : IsOpen (Set.univ : Set g32m_Domain) ∧ (Set.univ : Set g32m_Domain).Nonempty :=
  ⟨isOpen_univ, ⟨⟨0, g32m_zero_mem⟩, trivial⟩⟩

/-- Chain check toward the field `spread` of `g32a_premises`: for the concrete family, S6
gives its exact shape with `C = {univ}` from any nonempty open set of algebraic fibres. -/
example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) {U : Set g32m_Domain}
    (hU : IsOpen U) (hne : U.Nonempty) (hAlg : ∀ m ∈ U, g32t_WeilAlg (F.univ m)) :
    ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C := by
  refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
  · rintro Z rfl
    exact isClosedAnalytic_univ
  · rw [Set.sUnion_singleton, Set.eq_univ_iff_forall, hF]
    rw [hF] at hAlg
    exact hk_weilAlg_of_open hU hne hAlg

/-- Chain check with the remaining bundle fields: dominance, the stage-3 supply and the
bundle's own `transport` field give the open set, so `spread` follows from the other fields
for the concrete family. S7 will replace `B.transport` by a source-to-target input. -/
example (B : g32a_premises) (hF : B.F.univ = b60b_univ) :
    ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧
      {m | g32t_WeilAlg (B.F.univ m)} = ⋃₀ C := by
  obtain ⟨U, hU, hne, hUs⟩ := g32r_dominant B.F B.P B.R
  refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
  · rintro Z rfl
    exact isClosedAnalytic_univ
  · rw [Set.sUnion_singleton, Set.eq_univ_iff_forall, hF]
    refine hk_weilAlg_of_open hU hne fun m hm => ?_
    obtain ⟨s, hs⟩ := hUs m hm
    rw [← hF]
    exact (B.transport _ _ hs).1 (g32s_fiber_alg B.P B.h46 s)

end HodgeLean.Foundations.Program

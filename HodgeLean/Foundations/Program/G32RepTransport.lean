import HodgeLean.Foundations.Program.G32RepTransportProofs

/-!
# G32 representation stages E and G (FROZEN SPEC)

Stage E of `docs/specs/RepFoundations.md` for an arbitrary finite group, and stage G of
`docs/specs/G32RepStages.md` for a realized cover `X : g32p_Cover A` of a G32 sixfold:

* stage E: the restriction multiplicity `papersMult H σ χ` is the dimension of the
  `(H, χ)`-eigenspace of `σ`;
* stage G: every `u ∈ g32c_U X` preserves the complexified primitive part of a supplier; its
  transport `g32c_restrict … u` to `H¹(P_χ; ℂ)` is intertwined with `u` by `proj^*` and commutes
  with the cyclotomic action; `proj^*` maps the eigenspace `V_t` of an embedding with
  `t(ζ) = exp(2πi/m)^k` onto the `χc^k`-eigenspace of `H′`; the transport has determinant one;
  and the complementary line of `t` carries the character `charOf(a(χc^k))⁻¹`, which is the
  input `hco` of `g32c_gamma_invariant_of` for one supplier.

These are implications from the fields of `g32p_Cover` and `g32p_Part` (`X.aut_mul`, `X.mult`,
`X.pol_nondeg`, `X.pol_inv`, `retract`, `image`, `equivariant`), the stages A–D of
`G32RepStages.lean` and the general foundations of `RepFoundations.lean`. Nothing here asserts that
a `g32p_Cover` exists, an algebraicity, a character comparison, the Weil block, or any of the three
set-aside contraction statements; stages F and H and the restoration module are listed in
`docs/specs/G32RepTransport.md`. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations

/-! ## Stage E: restriction multiplicities -/

/-- **Restriction multiplicities are eigenspace dimensions.** For a finite-dimensional
representation `σ` of a finite group `G`, a subgroup `H` and a character `χ` of `H`,
`⟨σ|_H, χ⟩ = dim Hom_H(χ, σ|_H)` (`papersMult`) equals `dim σ^{H, χ}`: an `H`-map from the line
`χ` is determined by its value at `1`, which lies in `rfd_eigen σ.ρ H χ`, and every vector there
is such a value.
Source: Serre, *Linear representations of finite groups*, §2.6 and §7.1 (Frobenius reciprocity
for a linear character); G32 v0.16, Subsection 4.2 (`V_χ = ⊕_τ Hom_{H′}(χ, τ|_{H′}) ⊗ M_τ`);
`papersMult`, `rfd_eigen`. -/
theorem rfd_finrank_eigen_eq_papersMult {G : Type} [Group G] [Fintype G] (σ : FDRep ℂ G)
    (H : Subgroup G) (χ : H →* ℂˣ) :
    Module.finrank ℂ (rfd_eigen σ.ρ H χ) = papersMult H σ χ :=
  rfd_finrank_eigen_eq_papersMult_aux σ H χ

/-- The multiplicity vanishes exactly when the eigenspace does. -/
example {G : Type} [Group G] [Fintype G] (σ : FDRep ℂ G) (H : Subgroup G) (χ : H →* ℂˣ) :
    papersMult H σ χ = 0 ↔ rfd_eigen σ.ρ H χ = ⊥ := by
  rw [← rfd_finrank_eigen_eq_papersMult σ H χ, Submodule.finrank_eq_zero]

end HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

/-! ## Stage G: primitive-part transport -/

/-- **`U` preserves the primitive part.** For a supplier `S` and `u ∈ U`, `u` maps the
complexified rational primitive part `ℂ ⊗ g32p_primitive X.aut S` into itself: the primitive part
is a finite intersection of kernels of polynomials in the pullbacks `(aut h)^*`, `h ∈ H′`, its
complexification is the intersection of the complexified kernels, and `u` commutes with every
`(aut h)^*_ℂ` (second clause of `g32c_U`).
Source: G32 v0.16, Subsections 4.1 (the primitive part `P_χ`) and 4.2 (`U` is the centralizer of
`G`); `g32p_primitive`, `g32c_U`, Mathlib `Submodule.baseChange`. -/
theorem g32rep_primitive_preserved (X : g32p_Cover A) (S : g32p_Supplier)
    {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X) :
    ∀ x ∈ (g32p_primitive X.aut S).baseChange ℂ,
      u x ∈ (g32p_primitive X.aut S).baseChange ℂ :=
  g32rep_primitive_preserved_aux X S hu

/-- A complexified primitive class stays in the complexified primitive part. -/
example (X : g32p_Cover A) (S : g32p_Supplier) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)}
    (hu : u ∈ g32c_U X) {x : HQ X.J 1} (hx : x ∈ g32p_primitive X.aut S) :
    u ((1 : ℂ) ⊗ₜ[ℚ] x) ∈ (g32p_primitive X.aut S).baseChange ℂ :=
  g32rep_primitive_preserved X S hu _ (Submodule.tmul_mem_baseChange_of_mem 1 hx)

/-- **`proj^*` intertwines the transport with `u`.** For an admissible supplier and `u ∈ U`,
`proj^* ∘ g32c_restrict incl proj N u = u ∘ proj^*` on `H¹(P_χ; ℂ)`: `incl ≫ proj = [N]` gives
`incl^* ∘ proj^* = N`, so `proj^* ∘ incl^*` is `N` on `range proj^* = ℂ ⊗ g32p_primitive`
(`image`), which `u` preserves (`g32rep_primitive_preserved`).
Source: G32 v0.16, Subsection 4.1 (`P_χ` the image of `N π_χ`); `g32p_Part.retract`,
`g32p_Part.image`, `spec_homPullback_comp`, `spec_homPullback_zpow_degree`, `g32c_restrict`. -/
theorem g32rep_restrict_proj (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X) :
    (homPullback (X.part S hS).proj 1).baseChange ℂ ∘ₗ
        g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u =
      u ∘ₗ (homPullback (X.part S hS).proj 1).baseChange ℂ :=
  g32rep_restrict_proj_aux X S hS hu

/-- The intertwining, applied to a vector. -/
example (X : g32p_Cover A) (S : g32p_Supplier) (hS : g32p_Admissible X.aut S)
    {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X)
    (y : ℂ ⊗[ℚ] HQ (X.part S hS).P 1) :
    (homPullback (X.part S hS).proj 1).baseChange ℂ
        (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u y) =
      u ((homPullback (X.part S hS).proj 1).baseChange ℂ y) :=
  LinearMap.congr_fun (g32rep_restrict_proj X S hS hu) y

/-- **The transport commutes with the cyclotomic action.** For an admissible supplier, `u ∈ U`
and `a ∈ ℚ(μ_m)`, `g32c_restrict … u` commutes with the complexified field action
`cyc_scalar a`: `ℚ(μ_m) = ℚ[ζ]`, `ζ` is a field value of `H′` (`χ` is onto), `proj^*` carries
`cyc_scalar (ζ^{χ h})` to `(aut h)^*` (`equivariant`), `u` commutes with `(aut h)^*`, and `proj^*` is
injective (`incl^* ∘ proj^* = N`) with `g32rep_restrict_proj`.
Source: G32 v0.16, Subsection 4.1 (`F_χ` acts on `P_χ` through `H′/ker χ`); `g32p_Part.equivariant`,
`g32p_Part.retract`, `g32rep_restrict_proj`. -/
theorem g32rep_restrict_cyc (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X)
    (a : cyc_Field S.m) :
    g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u ∘ₗ
        (cyc_scalar (X.part S hS).act.cyc_coordinates a).baseChange ℂ =
      (cyc_scalar (X.part S hS).act.cyc_coordinates a).baseChange ℂ ∘ₗ
        g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u :=
  g32rep_restrict_cyc_aux X S hS hu a

/-- The transport preserves every eigenspace `V_t` of the cyclotomic action. -/
example (X : g32p_Cover A) (S : g32p_Supplier) (hS : g32p_Admissible X.aut S)
    {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X) (t : cyc_Field S.m →ₐ[ℚ] ℂ)
    {y : ℂ ⊗[ℚ] HQ (X.part S hS).P 1}
    (hy : y ∈ cyc_eigenspace (X.part S hS).act.cyc_coordinates t) :
    g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u y ∈
      cyc_eigenspace (X.part S hS).act.cyc_coordinates t := by
  simp only [cyc_eigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hy ⊢
  intro a
  rw [← LinearMap.comp_apply, ← g32rep_restrict_cyc X S hS hu a, LinearMap.comp_apply, hy a,
    map_smul]

/-- **`proj^*` maps `V_t` onto an eigenspace of `H′`.** For an admissible supplier, the complex
character `χc` of `H′` with `χc(h) = exp(2πi/m)^{χ(h)}`, and an embedding `t` with
`t(ζ) = exp(2πi/m)^k`, the image under `proj^*` of the eigenspace `V_t` is the
`χc^k`-eigenspace `(ℂ ⊗ H¹(J))^{H′, χc^k}`: `equivariant` gives `(aut h)^* proj^* y =
t(ζ)^{χ(h)} proj^* y` for `y ∈ V_t`; conversely `k` is prime to `m` (`t(ζ)` is primitive), so a
`χc^k`-eigenvector is fixed by `ker χ` and killed by `Φ_m((aut h)^*)` for `χ(h) = 1`, hence lies in
`ℂ ⊗ g32p_primitive = range proj^*` (`image`), and injectivity of `proj^*` places its preimage
in `V_t`.
Source: G32 v0.16, Subsection 4.1 (`V_t` and the action of `H′` by `χ`) and the proof of
Proposition 4.6 (`det(u | V_χ)`); `g32p_Part.equivariant`, `g32p_Part.image`, `cyc_eigenspace`,
`rfd_eigen`. -/
theorem g32rep_proj_eigen (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    (k : ℤ) (t : cyc_Field S.m →ₐ[ℚ] ℂ) (ht : t (g32p_zeta S) = g32p_root S.m ^ k) :
    (cyc_eigenspace (X.part S hS).act.cyc_coordinates t).map
        ((homPullback (X.part S hS).proj 1).baseChange ℂ) =
      rfd_eigen (g32rep_rep X) S.H (χc ^ k) :=
  g32rep_proj_eigen_aux X S hS χc hχc k t ht

/-- A vector of `V_t` is carried to a `χc^k`-eigenvector of `H′`. -/
example (X : g32p_Cover A) (S : g32p_Supplier) (hS : g32p_Admissible X.aut S)
    (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    (k : ℤ) (t : cyc_Field S.m →ₐ[ℚ] ℂ) (ht : t (g32p_zeta S) = g32p_root S.m ^ k)
    {y : ℂ ⊗[ℚ] HQ (X.part S hS).P 1}
    (hy : y ∈ cyc_eigenspace (X.part S hS).act.cyc_coordinates t) :
    (homPullback (X.part S hS).proj 1).baseChange ℂ y ∈ rfd_eigen (g32rep_rep X) S.H (χc ^ k) := by
  rw [← g32rep_proj_eigen X S hS χc hχc k t ht]
  exact Submodule.mem_map_of_mem hy

/-- **The transport has determinant one.** For an admissible supplier and `u ∈ U`,
`det(g32c_restrict incl proj N u) = 1`: by `g32rep_restrict_proj` the transport is `u` restricted to
`ℂ ⊗ g32p_primitive = ⊕_{a ∈ (ℤ/m)ˣ} (ℂ ⊗ H¹(J))^{H′, χc^a}`; the eigenspaces of `a` and `-a` are
paired by the polarization form, so `u` acts there through `∏_σ e_σ^{n_σ}` with `n_σ = n_σ̄`, and
`e_σ̄ e_σ = 1`, `e_θ² = 1` with `n_θ` even, `e_σ = 1` for orthogonal `σ`, `M_σ = 0` for
`m_σ ≤ 0` (stages C and D).
Source: G32 v0.16, Subsection 4.2 and the proof of Proposition 4.6; `g32rep_restrict_proj`,
`g32rep_conj`, `g32rep_parity`, `g32rep_orthogonal`, `g32rep_mult_eq_bot`, `rfd_det_eigen`. -/
theorem g32rep_det_restrict (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X) :
    LinearMap.det (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u) = 1 :=
  g32rep_det_restrict_aux X S hS hu

/-- The transport of `u ∈ U` is invertible. -/
example (X : g32p_Cover A) (S : g32p_Supplier) (hS : g32p_Admissible X.aut S)
    {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X) :
    LinearMap.det (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u) ≠ 0 := by
  rw [g32rep_det_restrict X S hS hu]
  exact one_ne_zero

/-- **The complementary line carries `charOf(a(χc^k))⁻¹`.** For an admissible supplier, an
enumeration `(τ, τ̄, θ)`, an embedding `t` with `t(ζ) = exp(2πi/m)^k` and `u ∈ U`, the transport
acts on the complementary line `det(⊕_{s ≠ t} V_s)` (`g32c_coLine` in degree
`2k (φ(m) - 1)`) by `g32c_charOf X τ θ u hu (papersA τ τbar θ S.H (χc ^ k))⁻¹`: the transport
preserves each `V_s` (`g32rep_restrict_cyc`), so it acts on the line by `∏_{s ≠ t} det(u | V_s)`,
which is `det(u | V_t)⁻¹` by `g32rep_det_restrict`; `g32rep_proj_eigen` and
`g32rep_restrict_proj` identify `det(u | V_t)` with `det(u | (ℂ ⊗ H¹(J))^{H′, χc^k})`, and that is
`charOf(a(χc^k))` by `rfd_det_eigen`, `rfd_finrank_eigen_eq_papersMult` and stages C and D (stage
F). This is the hypothesis `hco` of `g32c_gamma_invariant_of` for one supplier.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "The correspondence" (`Z_i` and the
characters of `U`); `g32c_gamma_invariant_of`, `g32c_coLine`, `g32c_charOf`, `papersA`. -/
theorem g32rep_hco (X : g32p_Cover A) (S : g32p_Supplier) (hS : g32p_Admissible X.aut S)
    (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    {I K : Type*} [Fintype I] [Fintype K] (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ) :
    ∀ (k : ℤ) (t : cyc_Field S.m →ₐ[ℚ] ℂ), t (g32p_zeta S) = g32p_root S.m ^ k →
      ∀ (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X),
      ∀ Z ∈ g32c_coLine (X.part S hS).act.cyc_coordinates t
          (2 * (X.part S hS).k * (S.m.totient - 1)),
        exteriorPower.map (2 * (X.part S hS).k * (S.m.totient - 1))
            (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u) Z =
          (g32c_charOf X τ θ u hu (papersA τ τbar θ S.H (χc ^ k)))⁻¹ • Z :=
  g32rep_hco_aux X S hS χc hχc τ τbar θ hE

/-- The hypothesis `hco` of `g32c_gamma_invariant_of`, verbatim, for a family of suppliers. -/
example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (χc : ∀ j, (S j).H →* ℂˣ)
    (hχc : ∀ j h, ((χc j h : ℂˣ) : ℂ) =
      g32p_root (S j).m ^ (Multiplicative.toAdd ((S j).χ h)).val)
    {I K : Type*} [Fintype I] [Fintype K] (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ) :
    ∀ (j : Fin r) (k : ℤ) (t : cyc_Field (S j).m →ₐ[ℚ] ℂ),
      t (g32p_zeta (S j)) = g32p_root (S j).m ^ k →
      ∀ (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X),
      ∀ Z ∈ g32c_coLine (X.part (S j) (hS j)).act.cyc_coordinates t
          (2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1)),
        exteriorPower.map (2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1))
            (g32c_restrict (X.part (S j) (hS j)).incl (X.part (S j) (hS j)).proj
              (X.part (S j) (hS j)).N u) Z =
          (g32c_charOf X τ θ u hu (papersA τ τbar θ (S j).H (χc j ^ k)))⁻¹ • Z :=
  fun j => g32rep_hco X (S j) (hS j) (χc j) (hχc j) τ τbar θ hE

end HodgeLean.Foundations.Program

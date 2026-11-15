import HodgeLean.Foundations.Program.G32RepWeilProofs

/-!
# G32 representation stage H: the Weil block (FROZEN SPEC)

Stage H of `docs/specs/G32RepStages.md` and `docs/specs/G32RepTransport.md`, for a realized cover
`X : g32p_Cover A` of a G32 sixfold, with `ρ̄ = g32p_rhoDual = FDRep.of (Representation.dual
g32p_rho.ρ)`:

* the image of `projA^*` in `ℂ ⊗ H¹(J)` is `ℓ ⊗ M_ρ ⊕ ℓ̄ ⊗ M_ρ̄` for nonzero vectors `x ∈ ρ`,
  `y ∈ ρ̄` (the lines `ℓ = ℂx`, `ℓ̄ = ℂy`), and every `u ∈ g32c_U X` preserves it;
* the Weil eigenspace `A.W.Vs` is carried by `projA^*` onto the intersection of that image with
  an eigenspace of `(aut X.centre)^*` for a primitive cube root of unity;
* the transport `g32c_restrict X.inclA X.projA X.NA u` preserves `A.W.Vs`, which has dimension
  six, and its determinant there is `e_ρ(u)^ε` for one sign `ε` independent of `u`.

These are implications from the fields of `g32p_Cover` (`retractA`, `groupRing`, `rhoBlock`,
`dimA`, `mult`, `centre_eq`, `weil`, `pol_nondeg`, `pol_inv`), the simplicity and multiplicities
of `g32p_rho` and `g32p_rhoDual` (`g32p_rho_simple`, `g32p_rhoDual_simple`, `g32p_rho_cwMult`,
`g32p_rhoDual_cwMult`, `g32p_rhoDual_conjugate`), the stages A–G of `G32RepStages.lean` and
`G32RepTransport.lean`, and the general foundations of `RepFoundations.lean`. Nothing here asserts
that a `g32p_Cover` exists, an algebraicity, a character comparison or a contraction. The
restoration of `g32c_weil_character` and `g32c_gamma_invariant` from these statements is the
module `G32ContractionRestored.lean`. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

/-- **The image of `projA^*` is `ℓ ⊗ M_ρ ⊕ ℓ̄ ⊗ M_ρ̄`.** There are nonzero `x ∈ ρ` and `y ∈ ρ̄`
such that the complexified image of `projA^* : H¹(A) → H¹(J)` is the sum of
`{φ x | φ ∈ M_ρ}` and `{ψ y | ψ ∈ M_ρ̄}`: `projA^* ∘ inclA^* = Σ_g c_g (aut g)^*` (`groupRing`) has the
same image as `projA^*` (`retractA`), the image of an element `e` of `ℤ[G]` is
`⊕_τ e(τ) ⊗ M_τ` (`rfd_eval_bijective`), `rhoBlock` leaves only `τ = ρ, ρ̄`, `e` acts on `ρ̄` by the
complex conjugate of its action on `ρ` (`ρ` is unitary), and the dimension count
`12 = r (dim M_ρ + dim M_ρ̄) = 12 r` (`dimA`, `mult`, `g32p_rho_cwMult`, `g32p_rhoDual_cwMult`) gives
`rank e(ρ) = rank e(ρ̄) = 1`.
Source: G32 v0.16, Subsection 3.2 (Definition 3.2 and Lemma 3.3, `A_ρ(C)` as the image of an
element of `ℤ[G]`) and the proof of Proposition 4.6; Serre, *Linear representations of finite
groups*, §2.6, Theorem 8; `g32p_Cover.groupRing`, `g32p_Cover.rhoBlock`, `rfd_eval_bijective`. -/
theorem g32rep_projA_range (X : g32p_Cover A) :
    ∃ (x : g32p_rho) (y : g32p_rhoDual), x ≠ 0 ∧ y ≠ 0 ∧
      LinearMap.range ((homPullback X.projA 1).baseChange ℂ) =
        (rfd_mult g32p_rho (g32rep_rep X)).map (LinearMap.applyₗ x) ⊔
          (rfd_mult g32p_rhoDual (g32rep_rep X)).map (LinearMap.applyₗ y) :=
  g32rep_projA_range_aux X

/-- The `ρ`-summand `ℓ ⊗ M_ρ` lies in the image of `projA^*`. -/
example (X : g32p_Cover A) :
    ∃ x : g32p_rho, x ≠ 0 ∧ (rfd_mult g32p_rho (g32rep_rep X)).map (LinearMap.applyₗ x) ≤
      LinearMap.range ((homPullback X.projA 1).baseChange ℂ) := by
  obtain ⟨x, y, hx, -, h⟩ := g32rep_projA_range X
  exact ⟨x, hx, h ▸ le_sup_left⟩

/-- **`U` preserves the image of `projA^*`.** For `u ∈ U`, `u` maps the complexified image of
`projA^*` into itself: that image is the image of `Σ_g c_g (aut g)^*_ℂ` (`groupRing`, and
`inclA^* ∘ projA^* = NA` from `retractA`), and `u` commutes with every `(aut g)^*_ℂ` (second clause
of `g32c_U`).
Source: G32 v0.16, Subsections 3.2 (Lemma 3.3) and 4.2 (`U` is the centralizer of `G`);
`g32p_Cover.groupRing`, `g32p_Cover.retractA`, `spec_homPullback_mul`, `g32c_U`. -/
theorem g32rep_projA_preserved (X : g32p_Cover A) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)}
    (hu : u ∈ g32c_U X) :
    ∀ z ∈ LinearMap.range ((homPullback X.projA 1).baseChange ℂ),
      u z ∈ LinearMap.range ((homPullback X.projA 1).baseChange ℂ) :=
  g32rep_projA_preserved_aux X hu

/-- The image under `u` of a pulled-back class is again pulled back from `A`. -/
example (X : g32p_Cover A) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X)
    (a : ℂ ⊗[ℚ] HQ A.X 1) :
    ∃ b, (homPullback X.projA 1).baseChange ℂ b = u ((homPullback X.projA 1).baseChange ℂ a) :=
  g32rep_projA_preserved X hu _ (LinearMap.mem_range_self _ a)

/-- **The Weil eigenspace inside the block.** For a primitive cube root of unity `c`, `projA^*`
carries the Weil eigenspace `A.W.Vs` (the `i√3`-eigenspace of the complexified `J`) onto the
intersection of the image of `projA^*` with the `c`-eigenspace of `(aut X.centre)^*_ℂ`: by `weil`,
`projA^* ∘ J = projA^* + 2 (aut X.centre)^* ∘ projA^*`, so on the image of `projA^*` the centre acts
by `(J - 1)/2`, and `c = (i√3 - 1)/2`; `projA^*` is injective (`retractA`).
Source: G32 v0.16, Subsection 3.2 (Lemma 3.6, the Weil action of `√-3` induced by `1 + 2λI`);
`g32p_Cover.weil`, `g32p_Cover.retractA`, `HodgeBlocks.WeilAction.Vs`. -/
theorem g32rep_weil_eigenspace (X : g32p_Cover A) :
    ∃ c : ℂ, c ^ 2 + c + 1 = 0 ∧
      A.W.Vs.map ((homPullback X.projA 1).baseChange ℂ) =
        LinearMap.range ((homPullback X.projA 1).baseChange ℂ) ⊓
          Module.End.eigenspace (g32rep_rep X X.centre) c :=
  g32rep_weil_eigenspace_aux X

/-- A Weil vector is pulled back to an eigenvector of the centre. -/
example (X : g32p_Cover A) :
    ∃ c : ℂ, c ^ 2 + c + 1 = 0 ∧ ∀ y ∈ A.W.Vs,
      (homPullback X.projA 1).baseChange ℂ y ∈ Module.End.eigenspace (g32rep_rep X X.centre) c := by
  obtain ⟨c, hc, h⟩ := g32rep_weil_eigenspace X
  refine ⟨c, hc, fun y hy => ?_⟩
  have hm : (homPullback X.projA 1).baseChange ℂ y ∈
      A.W.Vs.map ((homPullback X.projA 1).baseChange ℂ) := Submodule.mem_map_of_mem hy
  rw [h] at hm
  exact hm.2

/-- **The transport of `U` preserves the Weil eigenspace.** For `u ∈ U`,
`g32c_restrict X.inclA X.projA X.NA u = NA⁻¹ · inclA^* ∘ u ∘ projA^*` maps `A.W.Vs` into itself:
for `y ∈ A.W.Vs`, `u (projA^* y)` lies in the image of `projA^*` (`g32rep_projA_preserved`) and in
the same eigenspace of the centre (`u` commutes with `(aut X.centre)^*`), so it is `projA^* y'` with
`y' ∈ A.W.Vs` (`g32rep_weil_eigenspace`), and the transport sends `y` to
`NA⁻¹ inclA^* projA^* y' = y'` (`retractA`).
Source: G32 v0.16, Subsection 3.2 (Lemma 3.6) and the proof of Proposition 4.6 (`U` acts on
`W_K(A)`); `g32rep_projA_preserved`, `g32rep_weil_eigenspace`, `g32c_restrict`. -/
theorem g32rep_weil_preserved (X : g32p_Cover A) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)}
    (hu : u ∈ g32c_U X) :
    ∀ y ∈ A.W.Vs, g32c_restrict X.inclA X.projA X.NA u y ∈ A.W.Vs :=
  g32rep_weil_preserved_aux X hu

/-- The transport sends scalar multiples of Weil vectors into `A.W.Vs`. -/
example (X : g32p_Cover A) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X)
    {y : ℂ ⊗[ℚ] HQ A.X 1} (hy : y ∈ A.W.Vs) (a : ℂ) :
    g32c_restrict X.inclA X.projA X.NA u (a • y) ∈ A.W.Vs :=
  g32rep_weil_preserved X hu _ (A.W.Vs.smul_mem a hy)

/-- **The Weil eigenspace has dimension six.** `dim_ℚ H¹(A) = 12` (`dimA`), the complexified `J`
is diagonalizable with eigenvalues `±i√3` and the two eigenspaces are complementary
(`HodgeBlocks.WeilAction.isCompl_Vs_Vsbar`) and exchanged by complex conjugation
(`HodgeBlocks.WeilAction.finrank_Vsbar_eq_Vs`).
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, LNM 1594,
§5 (the eigenspaces of an imaginary quadratic action); `g32p_Cover.dimA`. -/
theorem g32rep_weil_finrank (X : g32p_Cover A) : Module.finrank ℂ A.W.Vs = 6 :=
  g32rep_weil_finrank_aux X

/-- The Weil eigenspace is nonzero. -/
example (X : g32p_Cover A) : A.W.Vs ≠ ⊥ := by
  intro h
  have := g32rep_weil_finrank X
  rw [h, finrank_bot] at this
  exact absurd this (by norm_num)

/-- **The uniform sign of the Weil block.** There is one sign `ε` such that for every `u ∈ U` the
determinant of the transport on `A.W.Vs` is `e_ρ(u)^ε`: by `g32rep_weil_eigenspace` and
`g32rep_projA_range`, `projA^*(A.W.Vs)` is the summand of the block on which the centre acts by
`c`, which is `ℓ ⊗ M_ρ` when `λ = c` (`centre_eq`: the centre acts by `λ` on `ρ` and by `λ̄ ≠ λ` on
`ρ̄`) and `ℓ̄ ⊗ M_ρ̄` otherwise, a choice that does not depend on `u`. The transport is conjugate
through `projA^*` to `u` on that summand, and `φ ↦ φ x` is an isomorphism `M_ρ ≅ ℓ ⊗ M_ρ`
intertwining `u ∘ -` with `u` (`ρ` simple), so the determinant is `e_ρ(u)`, or `e_ρ̄(u) = e_ρ(u)⁻¹`
(`rfd_det_mul_dual` with `g32p_rhoDual_conjugate` and the form of `g32rep_form_spec`, as in
`g32rep_conj`).
Source: G32 v0.16, proof of Proposition 4.6 (the character of `U` on `W_K(A)`, `e_ρ^{±1}`);
`rfd_det_eq_prod`, `rfd_det_mul_dual`, `g32rep_char_eq`, `g32p_Cover.centre_eq`. -/
theorem g32rep_weil_sign (X : g32p_Cover A) :
    ∃ ε : ℤˣ, ∀ (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X)
      (h : ∀ y ∈ A.W.Vs, g32c_restrict X.inclA X.projA X.NA u y ∈ A.W.Vs),
      LinearMap.det ((g32c_restrict X.inclA X.projA X.NA u).restrict h) =
        g32c_char X g32p_rho u hu ^ (ε : ℤ) :=
  g32rep_weil_sign_aux X

/-- When `e_ρ(u) = 1` the transport has determinant one on the Weil eigenspace. -/
example (X : g32p_Cover A) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X)
    (h : ∀ y ∈ A.W.Vs, g32c_restrict X.inclA X.projA X.NA u y ∈ A.W.Vs)
    (h1 : g32c_char X g32p_rho u hu = 1) :
    LinearMap.det ((g32c_restrict X.inclA X.projA X.NA u).restrict h) = 1 := by
  obtain ⟨ε, hε⟩ := g32rep_weil_sign X
  rw [hε u hu h, h1, one_zpow]

end HodgeLean.Foundations.Program

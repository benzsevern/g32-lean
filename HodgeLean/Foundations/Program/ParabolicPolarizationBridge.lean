import HodgeLean.Foundations.Program.ParabolicPolarizationBridgeProofs

/-!
# H1: from discriminant `[-2]` to the parabolic-polarization comparison (FROZEN SPEC)

The frozen spec for `docs/briefs/cloud-spec-h1.md`; see `docs/specs/ParabolicPolarizationBridge.md`.
Each theorem is `:= <name>_aux …`, with its body in `ParabolicPolarizationBridgeProofs.lean`.

It claims the implication from `g32t_disc h = classNegTwo` to `g32d_ParabolicPolarization h`
for a polarized sixfold of Weil type `h : g32t_PolarizedWeil P`, with scale `c = 1`
(stage H1 of `docs/specs/G32RemainingPremises.md`, §1.3). The route is Landherr's
classification in rank six (`b60c_landherr`, `hermClass_rank_six_standard`) applied on both
sides and composed. Separately stated:

* the signature bridge from the eigenvalue count over `ℂ` to `hermSignature` of a Hermitian
  matrix form over `K = ℚ(√-3)`, for every size `n`, and its specialization to `g32H0 ζ`;
* the convention bridge: an isometry onto the matrix form of `M` gives a basis in which
  `LinearMap.toMatrix₂` is `M` itself (not its transpose or conjugate);
* the determinant class `[-2]` and the Landherr model of the printed form `g32H0 ζ`.

It does not claim that any fibre of the Prym family has discriminant `[-2]`: that is the
discriminant computation H2–H7 of the plan, and the field `hpol` follows from H1 only together
with it. Nothing here identifies `g32H0` with a cup product. HC no distance; AV milestone no
distance.
-/

noncomputable section
open Matrix
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
open HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-! ## The complex image of the printed matrix -/

/-- **`ζ` is a cube root of unity in `ℂ`.** The image of `ζ = (-1 + √-3)/2` under the embedding
`√-3 ↦ i√3` satisfies `ω² + ω + 1 = 0`, the hypothesis of `papers_g32_h0_signature`.
Source: G32 v0.16, Section 2; the standard presentation of `ℚ(√-3)`. -/
theorem hp_toComplex_zeta :
    hp_toComplex hp_zeta ^ 2 + hp_toComplex hp_zeta + 1 = 0 :=
  hp_toComplex_zeta_aux

example : hp_toComplex hp_zeta ≠ 1 := by
  intro h1
  have h := hp_toComplex_zeta
  rw [h1] at h
  norm_num at h

/-- **Entrywise image of the printed matrix.** The embedding carries `g32H0 ζ` over `K` to
`g32H0` evaluated at the complex image of `ζ`, since every entry is a rational affine
expression in `ζ`.
Source: G32 v0.16, proof of Proposition 6.3 (the matrix `h_0`); `g32H0`. -/
theorem hp_h0_map_complex :
    (g32H0 hp_zeta).map hp_toComplex = g32H0 (hp_toComplex hp_zeta) :=
  hp_h0_map_complex_aux

example : ((g32H0 hp_zeta).map hp_toComplex) 2 5 = -1/3 * hp_toComplex hp_zeta := by
  rw [hp_h0_map_complex]
  rfl

/-! ## The signature and convention bridges -/

/-- **Signature bridge.** For a matrix `M` over `K = ℚ(√-3)` whose complex image `A` is
Hermitian, `hermSignature` of the matrix form of `M` is the number of positive and the number
of negative eigenvalues of `A`. The real quadratic form `x ↦ re (h x x)` on `ℝ ⊗ K^n ≅ ℂ^n`
is `v ↦ vᴴ A v`, whose real signature is twice the complex one.
Source: Sylvester's law of inertia; the spectral theorem for Hermitian matrices (Mathlib
`Matrix.IsHermitian.eigenvalues`); G32 v0.16, proof of Proposition 6.3. -/
theorem hp_hermSignature_matrixForm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (QuadraticAlgebra ℚ (-3) 0))
    (A : Matrix (Fin n) (Fin n) ℂ) (hMA : M.map hp_toComplex = A) (hA : A.IsHermitian) :
    hermSignature (hp_matrixForm M) =
      ((Finset.univ.filter fun i => 0 < hA.eigenvalues i).card,
        (Finset.univ.filter fun i => hA.eigenvalues i < 0).card) :=
  hp_hermSignature_matrixForm_aux M A hMA hA

/-- A nonzero instance in rank one: `M = (-1)` has a Hermitian complex image. -/
example :
    let M : Matrix (Fin 1) (Fin 1) (QuadraticAlgebra ℚ (-3) 0) := !![-1]
    ∃ hA : (M.map hp_toComplex).IsHermitian,
      hermSignature (hp_matrixForm M) =
        ((Finset.univ.filter fun i => 0 < hA.eigenvalues i).card,
          (Finset.univ.filter fun i => hA.eigenvalues i < 0).card) := by
  intro M
  have hA : (M.map hp_toComplex).IsHermitian := by
    ext i j
    fin_cases i
    fin_cases j
    simp [M]
  exact ⟨hA, hp_hermSignature_matrixForm M _ rfl hA⟩

/-- **Convention bridge.** If a linear equivalence `f : W ≃ Kⁿ` carries `H` to the matrix form of
`M`, then in the basis `f⁻¹(eᵢ)` the Gram matrix `LinearMap.toMatrix₂` of `H` is `M`, entry
`(i, j)` being `H(f⁻¹ eᵢ, f⁻¹ eⱼ)`; neither its transpose nor its conjugate appears.
Source: Mathlib `LinearMap.toMatrix₂_apply`, `Matrix.toLinearMapₛₗ₂`. -/
theorem hp_toMatrix₂_of_isometry {W : Type*} [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] {n : ℕ}
    (H : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (M : Matrix (Fin n) (Fin n) (QuadraticAlgebra ℚ (-3) 0))
    (f : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0] (Fin n → QuadraticAlgebra ℚ (-3) 0))
    (hf : ∀ x y, hp_matrixForm M (f x) (f y) = H x y) :
    LinearMap.toMatrix₂ ((Pi.basisFun _ (Fin n)).map f.symm)
      ((Pi.basisFun _ (Fin n)).map f.symm) H = M :=
  hp_toMatrix₂_of_isometry_aux H M f hf

/-- The identity of `K⁶` and the printed form satisfy the hypothesis. -/
example :
    LinearMap.toMatrix₂
      ((Pi.basisFun (QuadraticAlgebra ℚ (-3) 0) (Fin 6)).map (LinearEquiv.refl _ _).symm)
      ((Pi.basisFun (QuadraticAlgebra ℚ (-3) 0) (Fin 6)).map (LinearEquiv.refl _ _).symm)
      hp_h0Form = g32H0 hp_zeta :=
  hp_toMatrix₂_of_isometry hp_h0Form (g32H0 hp_zeta) (LinearEquiv.refl _ _) fun _ _ => rfl

/-! ## The printed form on `K⁶` -/

/-- **The printed form is Hermitian.** `star (h₀(x, y)) = h₀(y, x)`, because `g32H0 ζ` equals
its conjugate transpose for `ζ̄ = -1 - ζ`.
Source: G32 v0.16, proof of Proposition 6.3; `papers_g32_h0_isHermitian` (over `ℂ`). -/
theorem hp_h0_isSymm : hp_h0Form.IsSymm :=
  hp_h0_isSymm_aux

example : hp_h0Form.IsSymm := hp_h0_isSymm

/-- **The printed form is nondegenerate**, since `det g32H0 ζ = -2/81 ≠ 0`.
Source: G32 v0.16, proof of Proposition 6.3; `papers_g32_h0_det`. -/
theorem hp_h0_nondegenerate : hp_h0Form.Nondegenerate :=
  hp_h0_nondegenerate_aux

example : hp_h0Form.Nondegenerate := hp_h0_nondegenerate

/-- **Signature `(3, 3)` of the printed form over `K`** (the plan's `hp_h0_hermSignature`).
Source: G32 v0.16, proof of Proposition 6.3; `papers_g32_h0_signature` with
`hp_hermSignature_matrixForm`. -/
theorem hp_h0_hermSignature : hermSignature hp_h0Form = (3, 3) :=
  hp_h0_hermSignature_aux

/-- Chain check: the signature follows from the bridge and the complex eigenvalue count. -/
example : hermSignature hp_h0Form = (3, 3) := by
  have hs := papers_g32_h0_signature _ hp_toComplex_zeta
  rw [show hp_h0Form = hp_matrixForm (g32H0 hp_zeta) from rfl,
    hp_hermSignature_matrixForm (g32H0 hp_zeta) _ hp_h0_map_complex
      (papers_g32_h0_isHermitian _ hp_toComplex_zeta), hs.1, hs.2]

/-- **Determinant class `[-2]` of the printed form** (the plan's `hp_h0_detClass`):
`-2/81 = -2 · Nm(1/9)`.
Source: G32 v0.16, proof of Proposition 6.3; `papers_g32_h0_det`, `papers_g32_det_norm`;
F-1569 (1). -/
theorem hp_h0_detClass :
    detClass hp_h0Form hp_h0_isSymm hp_h0_nondegenerate = classNegTwo :=
  hp_h0_detClass_aux

/-- The class is not trivial. -/
example : detClass hp_h0Form hp_h0_isSymm hp_h0_nondegenerate ≠ 1 := by
  rw [hp_h0_detClass]
  exact class_neg_two_ne_one

/-- **Landherr model of the printed form.** `g32H0 ζ` on `K⁶` is isometric to the diagonal
model `b60_H = ⟨1, 1, 1, -1, -1, -2⟩`.
Source: Landherr, Abh. Math. Sem. Hamburg 11 (1936), 245–248, through
`hermClass_rank_six_standard`; G32 v0.16, Proposition 6.3. -/
theorem hp_h0_landherr :
    ∃ g : (Fin 6 → QuadraticAlgebra ℚ (-3) 0) ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin 6 → QuadraticAlgebra ℚ (-3) 0),
      ∀ x y, b60_H (g x) (g y) = hp_h0Form x y :=
  hp_h0_landherr_aux

/-- Chain check: the Landherr model follows from rank six, signature and class. -/
example :
    ∃ g : (Fin 6 → QuadraticAlgebra ℚ (-3) 0) ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin 6 → QuadraticAlgebra ℚ (-3) 0),
      ∀ x y, b60_H (g x) (g y) = hp_h0Form x y := by
  obtain ⟨g, hg⟩ := HermitianClass.hermClass_rank_six_standard _ hp_h0Form hp_h0_isSymm
    hp_h0_nondegenerate (by simp) hp_h0_hermSignature hp_h0_detClass
  exact ⟨g, hg⟩

/-! ## The bridge -/

/-- **H1, scale one** (the plan's `hp_parabolic_of_disc`). For a polarized sixfold of Weil type
for `ℚ(√-3)` with discriminant `[-2]`, some `K`-basis of `H¹(X; ℚ)` has Gram matrix exactly
`g32H0 ζ` for the Weil Hermitian form. Both forms are isometric to `b60_H`
(`b60c_landherr`, `hp_h0_landherr`); compose the isometries and apply
`hp_toMatrix₂_of_isometry`.
Source: G32 v0.16, Proposition 6.3; Landherr, Abh. Math. Sem. Hamburg 11 (1936), 245–248;
van Geemen, LNM 1594, §5.4. -/
theorem hp_parabolic_of_disc (P : g32t_Sixfold) (h : g32t_PolarizedWeil P)
    (hd : g32t_disc h = classNegTwo) :
    let hT := torusCohomology_cupProductOf P.X
    letI := hT.finite
    let E := polarizationForm hT h.nondegenerate
    let J := ⟨P.W.J, P.W.J_sq⟩
    let H := weilHermitian E J
      (by simpa [E, polarizationForm] using
        (isRosatiSkew_iff_dualForm h.nondegenerate P.W.J).1 h.rosati)
    ∃ e : Module.Basis (Fin 6) (QuadraticAlgebra ℚ (-3) 0) (WithJ (HQ P.X 1) J),
      LinearMap.toMatrix₂ e e H = g32H0 hp_zeta :=
  hp_parabolic_of_disc_aux P h hd

/-- Rank check: the conclusion forces `K`-rank six, so the space is not zero. -/
example (P : g32t_Sixfold) (h : g32t_PolarizedWeil P) (hd : g32t_disc h = classNegTwo) :
    Module.finrank (QuadraticAlgebra ℚ (-3) 0)
      (WithJ (HQ P.X 1) ⟨P.W.J, P.W.J_sq⟩) = 6 := by
  obtain ⟨e, -⟩ := hp_parabolic_of_disc P h hd
  simpa using Module.finrank_eq_card_basis e

/-- **H1** in the shape of the stage-5 premise: `g32d_ParabolicPolarization h`, with `c = 1`.
Source: G32 v0.16, Proposition 6.3; `hp_parabolic_of_disc`. -/
theorem hp_parabolicPolarization_of_disc (P : g32t_Sixfold) (h : g32t_PolarizedWeil P)
    (hd : g32t_disc h = classNegTwo) :
    g32d_ParabolicPolarization h :=
  hp_parabolicPolarization_of_disc_aux P h hd

/-- Chain check: scale one gives the premise. -/
example (P : g32t_Sixfold) (h : g32t_PolarizedWeil P) (hd : g32t_disc h = classNegTwo) :
    g32d_ParabolicPolarization h := by
  obtain ⟨e, he⟩ := hp_parabolic_of_disc P h hd
  exact ⟨⟨1, one_pos⟩, e, by simpa [hp_zeta] using he⟩

/-- Instance check at the origin of the bounded domain: the member `b60b_member` supplies a
polarized sixfold of Weil type with discriminant `[-2]`, so the hypotheses are satisfiable. -/
example : ∃ h : g32t_PolarizedWeil (b60b_univ ⟨0, g32m_zero_mem⟩),
    g32d_ParabolicPolarization h := by
  obtain ⟨h, hd⟩ := (g32t_isMember_iff _).1 (b60b_member ⟨0, g32m_zero_mem⟩)
  exact ⟨h, hp_parabolicPolarization_of_disc _ h hd⟩

/-- With `g32d_fiber_disc`, the premise is equivalent to discriminant `[-2]`. -/
example (P : g32t_Sixfold) (h : g32t_PolarizedWeil P) :
    g32d_ParabolicPolarization h ↔ g32t_disc h = classNegTwo :=
  ⟨fun H => g32d_fiber_disc (fun _ : Unit => P) (fun _ => h) (fun _ => H) (),
    hp_parabolicPolarization_of_disc P h⟩

/-- Chain check toward the field `g32a_premises.hpol`: fibre discriminants `[-2]` give the
field's type. -/
example (P : g32h_PrymFamily)
    (hdisc : ∀ s, g32t_disc (g32h_fiber_polarized P s) = classNegTwo) :
    ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s) :=
  fun s => hp_parabolicPolarization_of_disc _ _ (hdisc s)

end HodgeLean.Foundations.Program

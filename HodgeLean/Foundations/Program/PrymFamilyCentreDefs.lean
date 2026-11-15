import HodgeLean.Foundations.Program.PrymFamilyAssembly

/-! # B6-3g, parts 2 and 3: the centre on the saturated lattice and the generic sixfold

The central deck operator `b63d_centre` of B6-3d restricts to the saturated singular lattice
`Λ_s = b63l_parameterLattice … s` (`b63d_centre_range`, which has a body); so does the integral
expression `1 + 2ω` of `b63d_operator`, and on `Λ_s` it squares to `-3`
(`b63d_prymOperator_sq`, which has a body). These are the lattice operators that stage 3g carries
through the B5 marking of part 1.

For B5 data `(Λ, F, Q)` and a lattice endomorphism `φ` with `φ² = -n` preserving `F`, the model
operator of part 1 is a Weil action of `ℚ(√-n)` on `H¹` of the model (`b63g2_weilAction`); with
`n = 3` the model, its five instances, that action and `b63g_modelClass` form a `g32t_Sixfold`
(`b63g2_sixfold`). The two proof arguments of these definitions are binders, not selected
witnesses.

The rotation `b63g2_hex` of order three of `ℤ²` is used only by the checks.

No definition selects a witness from an open statement, and none is a proposition.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular HodgeLean.RealDefs
open HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.Symplectic HodgeLean.Papers
open scoped TensorProduct Manifold ContDiff

namespace HodgeLean.Foundations.Program

/-! ## The centre on the saturated lattice -/

/-- The central deck operator maps the saturated lattice into itself: `b63d_centre_range`, which
has a body.
Source: G32 v0.16, §3.3 and Appendix A; `b63d_centre_range`. -/
theorem b63g2_centre_mem (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    (x : b63l_parameterLattice b C hC V hV s) :
    b63d_centre b C hC V hV s x.val ∈ b63l_parameterLattice b C hC V hV s := by
  obtain ⟨Z, hZ⟩ := b63d_centre_range b C hC V hV s
  rw [← hZ x]
  exact (Z x).property

/-- **The central deck operator on the saturated lattice** `Λ_s`: the restriction of
`b63d_centre` (the sum of `g_*` over the central elements `g` with matrix `ω · 1`), which maps
`Λ_s` into itself by `b63d_centre_range`.
Source: G32 v0.16, §3.3 and Appendix A; Birkenhake–Lange, §12.2; `b63d_centre_range`. -/
def b63g2_centre (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V) :
    b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s where
  toFun x := ⟨b63d_centre b C hC V hV s x.val, b63g2_centre_mem b C hC V hV s x⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_zsmul _ _ _)

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    (x : b63l_parameterLattice b C hC V hV s) :
    (b63g2_centre b C hC V hV s x).val = b63d_centre b C hC V hV s x.val := rfl

/-- **The operator `1 + 2ω` on the saturated lattice** `Λ_s`, the restriction of
`b63d_operator`.
Source: G32 v0.16, §3.3 (the expression `1 + 2ω`); `b63d_operator`. -/
def b63g2_operator (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V) :
    b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s :=
  LinearMap.id + 2 • b63g2_centre b C hC V hV s

theorem b63g2_operator_val (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    (x : b63l_parameterLattice b C hC V hV s) :
    (b63g2_operator b C hC V hV s x).val = b63d_operator b C hC V hV s x.val := by
  simp [b63g2_operator, b63d_operator, b63g2_centre]

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V) :
    b63g2_operator b C hC V hV s 0 = 0 := map_zero _

/-- **`(1 + 2ω)² = -3` on the saturated lattice**: `b63d_prymOperator_sq` (which has a body)
gives an operator with this square and the same values as `b63d_operator`, which is
`b63g2_operator` because the inclusion of `Λ_s` is injective.
Source: G32 v0.16, §3.2–3.3; `b63d_prymOperator_sq`. -/
theorem b63g2_operator_sq (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV s)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV s)]
    [T2Space (b63l_parameterFibre b C V hV s)] [CompactSpace (b63l_parameterFibre b C V hV s)]
    [ConnectedSpace (b63l_parameterFibre b C V hV s)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV s ↦ g • x)) :
    ∀ x, b63g2_operator b C hC V hV s (b63g2_operator b C hC V hV s x) = (-3 : ℤ) • x := by
  obtain ⟨J, hJ, hsq⟩ := b63d_prymOperator_sq b C hC V hV s hG
  have h : ∀ x, b63g2_operator b C hC V hV s x = J x := fun x ↦
    Subtype.ext ((b63g2_operator_val b C hC V hV s x).trans (hJ x).symm)
  intro x
  rw [h, h, hsq]

/-! ## The generic Weil action and sixfold of B5 data -/

/-- **The Weil action of the model operator.** For B5 data and a lattice endomorphism `φ` with
`φ² = -n` whose complexification preserves `F`, the model operator `b63g_modelOperator` with the
relation of `b63g_dualOperator_sq` and the Hodge compatibility of `b63g_dualOperator_hodge` (both
with bodies), carried by `b63g_modelMap_sq` and `b63g_modelMap_filtration`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 and §5.5 (abelian
varieties with an action of an imaginary quadratic field); `HodgeBlocks.WeilAction`. -/
def b63g2_weilAction (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℤ) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-n) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian (b5_model Λ F hF Q))
        (spec_bettiDeRhamIso_abelian (b5_model Λ F hF Q))
        (hodgeDecomposition_of_abelian (b5_model Λ F hF Q))
        (torusCohomology_cupProductOf (b5_model Λ F hF Q))).weight1 n :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
  ⟨b63g_modelOperator Λ F hF Q hQ φ,
    b63g_dualOperator_sq _ n _ (b63g_modelMap_sq Λ F hF Q hQ n φ hsq),
    b63g_dualOperator_hodge _ _ (b63g_modelMap_filtration Λ F hF Q hQ φ hφ)⟩

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℤ) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-n) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    (b63g2_weilAction Λ F hF Q hQ n φ hsq hφ).J = b63g_modelOperator Λ F hF Q hQ φ := rfl

/-- **The sixfold of B5 data with an operator of square `-3`**: the B5 model with its five
instances, the Weil action of the model operator (as in `b63g2_weilAction` with `n = 3`) and the
degree-two class `b63g_modelClass`.
Source: G32 v0.16, Definition 2.1 and Lemma 3.3; `g32t_Sixfold`, `b63g_modelClass`. -/
def b63g2_sixfold (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-3 : ℤ) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    g32t_Sixfold :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI : IsCommMonObj (b5_model Λ F hF Q) := b5_commutative_aux Λ F hF Q hQ
  letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
  { X := b5_model Λ F hF Q
    W := ⟨b63g_modelOperator Λ F hF Q hQ φ,
      (b63g_dualOperator_sq _ 3 _ (b63g_modelMap_sq Λ F hF Q hQ 3 φ hsq)).trans (by norm_num),
      b63g_dualOperator_hodge _ _ (b63g_modelMap_filtration Λ F hF Q hQ φ hφ)⟩
    pol := b63g_modelClass Λ F hF Q hQ }

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-3 : ℤ) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).X = b5_model Λ F hF Q ∧
      (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).W.J = b63g_modelOperator Λ F hF Q hQ φ ∧
      (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).pol = b63g_modelClass Λ F hF Q hQ :=
  ⟨rfl, rfl, rfl⟩

/-- The Hodge number `h10` of `b63g2_sixfold` is the one of the Weil action `b63g2_weilAction`
with `n = 3`: the two actions have the same operator, and `ω_ℂ` of `((3 : ℤ) : ℚ)` is `ω_ℂ` of `3`.
Source: `g32h_h10`, `HodgeBlocks.WeilAction.Vs`. -/
theorem b63g2_sixfold_h10 (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-3 : ℤ) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    g32h_h10 (b63g2_sixfold Λ F hF Q hQ φ hsq hφ) =
      Module.finrank ℂ ↥((b63g2_weilAction Λ F hF Q hQ 3 φ hsq hφ).Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian (b5_model Λ F hF Q))
          (spec_bettiDeRhamIso_abelian (b5_model Λ F hF Q))
          (hodgeDecomposition_of_abelian (b5_model Λ F hF Q))
          (torusCohomology_cupProductOf (b5_model Λ F hF Q))).weight1.H (1, 0)) := by
  unfold g32h_h10 HodgeBlocks.WeilAction.Vs
  rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
    norm_num]
  rfl

/-- The Hodge number `h01` of `b63g2_sixfold` is the one of the Weil action `b63g2_weilAction`
with `n = 3`: the two actions have the same operator, and `ω_ℂ` of `((3 : ℤ) : ℚ)` is `ω_ℂ` of `3`.
Source: `g32h_h01`, `HodgeBlocks.WeilAction.Vs`. -/
theorem b63g2_sixfold_h01 (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-3 : ℤ) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    g32h_h01 (b63g2_sixfold Λ F hF Q hQ φ hsq hφ) =
      Module.finrank ℂ ↥((b63g2_weilAction Λ F hF Q hQ 3 φ hsq hφ).Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian (b5_model Λ F hF Q))
          (spec_bettiDeRhamIso_abelian (b5_model Λ F hF Q))
          (hodgeDecomposition_of_abelian (b5_model Λ F hF Q))
          (torusCohomology_cupProductOf (b5_model Λ F hF Q))).weight1.H (0, 1)) := by
  unfold g32h_h01 HodgeBlocks.WeilAction.Vs
  rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
    norm_num]
  rfl

/-- The Weil action of `b63g2_sixfold` is Rosati-skew for its class when `φ` is skew for `Q`:
`b63g_dualOperator_rosati` and `b63g_modelForm_skew` (both with bodies).
Source: Birkenhake–Lange, §5.1; `b63g_dualOperator_rosati`, `b63g_modelForm_skew`. -/
theorem b63g2_sixfold_rosati (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-3 : ℤ) • l) (hφ : F ≤ F.comap (b2_cplxMap φ))
    (hskew : ∀ l m, Q (φ l) m = -Q l (φ m)) :
    letI := (torusCohomology_cupProductOf (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).X).finite
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf
        (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).X) (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).pol)
      (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).W.J := by
  have h :=
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b63g_dualOperator_rosati _ _ _ (b63g_modelForm_skew Λ F hF Q hQ φ hskew)
  unfold b63g2_sixfold
  exact h

/-! ## A rotation of order three, for the checks -/

/-- **The rotation of order three of `ℤ²`**, `e₀ ↦ e₁`, `e₁ ↦ -e₀ - e₁`: multiplication by
`ω = e^{2πi/3}` on the Eisenstein lattice `ℤ + ℤω`. Used only by the checks.
Source: Birkenhake–Lange, §1.1 (the elliptic curve `ℂ ⧸ (ℤ + ℤω)` has `ω` as an
automorphism). -/
def b63g2_hex : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) :=
  (Matrix.toLin' !![0, -1; 1, -1]).toAddMonoidHom

example : b63g2_hex (Pi.single 0 1) = Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp [b63g2_hex]

/-- The rotation of order three in coordinates.
Source: direct computation with the matrix `!![0, -1; 1, -1]`. -/
theorem b63g2_hex_apply (l : Fin 2 → ℤ) : b63g2_hex l = ![-l 1, l 0 - l 1] := by
  ext i
  fin_cases i <;> (simp [b63g2_hex, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; try ring)

/-- The standard form in coordinates.
Source: direct computation with the matrix `!![0, 1; -1, 0]` of `b2_stdForm`. -/
theorem b63g2_stdForm_apply (l m : Fin 2 → ℤ) : b2_stdForm l m = l 0 * m 1 - l 1 * m 0 := by
  simp [b2_stdForm, Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

example : b2_stdForm (Pi.single 0 1) (Pi.single 1 1) = 1 := by
  simp [b63g2_stdForm_apply]

end HodgeLean.Foundations.Program

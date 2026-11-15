import HodgeLean.Foundations.Program.G32ContractionProofs

/-! # The G32 contraction, first stage (FROZEN SPEC)

Implication from the realization `g32p_Cover` of a fibre `A_ρ(C)` inside the Jacobian of its
`G₃₂`-cover, and from explicit admissible suppliers, to the first steps of the contraction in
the proof of G32 Proposition 4.6.

Claimed:
* the product `A_ρ × B`, `B = ∏_j P_j`, and the power `J^{r+1}`, with homomorphisms
  `ι₀ : A_ρ × B ⟶ J^{r+1}` and `π : J^{r+1} ⟶ A_ρ × B` compatible with the factor maps
  (`g32c_realization`);
* `π ∘ ι₀ = [N₀]` with `N₀ > 0`, and `ι₀^* ∘ π^* = N₀ⁿ` in degree `n` (`g32c_retraction`);
* the correspondence of a product class `pr^* a ∪ pr^* b` is the tensor contraction
  `x ↦ I(b ∪ x) a` (`g32c_contraction_tensor`);
* nonvanishing of the contraction against a nonzero rational determinant class on each
  target line (`g32c_coLine_mul_ne_zero`).

Not claimed: Milne's invariance or its transport to `Γ`, algebraicity of `Γ`, the complexified
correspondence, the conjugate line, rational descent, or `g32p_weilLine_algebraic`; the
existence of a realization `g32p_Cover`; the character comparison of `spec/p46`. The `U`-characters of the
supplier parts and of the Weil line, and the `U`-invariance of `Γ`, are set aside
(2026-11-05) until the representation foundations they need exist; see
`docs/specs/G32Contraction.md`. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

/-- **The correspondence of a product class is tensor contraction.** For `ξ = pr_Y^* a ∪ pr_B^* b`
on `Y × B` with `dim B = d`, the correspondence `cfd_corrAction` sends `x ∈ H^{2p}(B)` to
`I(b ∪ x) · a`. With `Y = A_ρ`, `a = w`, `b = ⊠_j Z_j` and `x = ⊠_j y_j` this is the contraction
`Γ_*(Y) = ± ∏_i c_{i,t_i}^{|n_i|} w` of G32 once each `b ∪ x` is evaluated.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "The contraction is nonzero"
(`Γ_*(Y) = pr_{2*}(pr_1^* Y ∪ Γ)`); Fulton, *Intersection Theory*, Proposition 8.1.1(c) and
§16.1; `cfd_projection_formula`, `cfd_projection_cross`. -/
theorem g32c_contraction_tensor (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (c p q e : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d) (hc : 2 * q + 2 * e = 2 * c)
    (hd : 2 * e + 2 * p = 2 * d) (a : HQ Y (2 * q)) (b : HQ B (2 * e)) (x : HQ B (2 * p)) :
    cfd_corrAction Y B d I c p q h
      ((cupProductOf (Y ⊗ B)).cup hc (homPullback (fst Y B) (2 * q) a)
        (homPullback (snd Y B) (2 * e) b)) x =
      I ((cupProductOf B).cup hd b x) • a :=
  g32c_contraction_tensor_aux Y B d hB I c p q e h hc hd a b x

example (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (c p q e : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d) (hc : 2 * q + 2 * e = 2 * c)
    (hd : 2 * e + 2 * p = 2 * d) (a : HQ Y (2 * q)) (b : HQ B (2 * e)) (x : HQ B (2 * p)) :
    cfd_corrAction Y B d I c p q h
      ((cupProductOf (Y ⊗ B)).cup hc (homPullback (fst Y B) (2 * q) a)
        (homPullback (snd Y B) (2 * e) b)) x =
      I ((cupProductOf B).cup hd b x) • a :=
  g32c_contraction_tensor Y B d hB I c p q e h hc hd a b x

/-- **The contraction is nonzero on each target line.** For a nonzero rational determinant wedge
`w` (an element of `cyc_wedges e`) and a nonzero `Z` in the wedges of `⊕_{s ≠ t} V_s`, the
product `Z ∧ w_ℂ` is nonzero: the component of `w_ℂ` on `det V_t` is nonzero
(`cyc_projection_ne_zero`), its components on the other lines are killed or land in a
different bidegree, and `⊕_{s ≠ t} V_s` and `V_t` are complementary.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "The contraction is nonzero" ("for
`t ≠ t_i` the product `v_{i,t} ∪ Z_i` contains `det V_{i,t}` twice and vanishes. Each `c_{i,t}`
is nonzero"); `cyc_projection_ne_zero`, `cyc_eigenline_decomposition`. -/
theorem g32c_coLine_mul_ne_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {m h : ℕ} [NeZero m] (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m))
    (t : cyc_Field m →ₐ[ℚ] ℂ) (n : ℕ) (Z : ⋀[ℂ]^n (ℂ ⊗[ℚ] V)) (hZ : Z ∈ g32c_coLine e t n)
    (hZ0 : Z ≠ 0) (w : ⋀[ℚ]^h V) (hw : w ∈ cyc_wedges e) (hw0 : w ≠ 0) :
    (Z : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] V)) *
      (HodgeBlocks.complexifyWedge h w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] V)) ≠ 0 :=
  g32c_coLine_mul_ne_zero_aux e t n Z hZ hZ0 w hw hw0

example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {m h : ℕ} [NeZero m] (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m))
    (t : cyc_Field m →ₐ[ℚ] ℂ) (n : ℕ) (Z : ⋀[ℂ]^n (ℂ ⊗[ℚ] V)) (hZ : Z ∈ g32c_coLine e t n)
    (hZ0 : Z ≠ 0) (w : ⋀[ℚ]^h V) (hw : w ∈ cyc_wedges e) (hw0 : w ≠ 0) :
    (Z : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] V)) *
      (HodgeBlocks.complexifyWedge h w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] V)) ≠ 0 :=
  g32c_coLine_mul_ne_zero e t n Z hZ hZ0 w hw hw0

variable {A : g32t_Sixfold}

/-- **Realization of `A_ρ × B` and of `J^{r+1}`.** For a realized fibre and a list of admissible
suppliers, the inclusion `ι₀ : A_ρ × B ⟶ J^{r+1}` and the projection `π : J^{r+1} ⟶ A_ρ × B`
are homomorphisms of abelian varieties, and they are compatible with the factor maps: `ι₀`
followed by the `j`-th projection of the power is the `j`-th factor projection followed by the
factor inclusion, and `π` followed by the `j`-th factor projection is the `j`-th projection of
the power followed by the factor projection, rescaled to the common degree `N₀`.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "Γ is algebraic" (the maps `ι₀` and `π`
built from the inclusions `X' ↪ J(C)` and the homomorphisms `N₀ e_{X'}`); Mumford, *Abelian
Varieties*, §4. -/
theorem g32c_realization (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    IsMonHom (g32c_incl X S hS) ∧ IsMonHom (g32c_proj X S hS) ∧
    g32c_incl X S hS ≫ g3_proj X.J (r + 1) 0 = fst A.X (g32c_B X S hS) ≫ X.inclA ∧
    (∀ j : Fin r, g32c_incl X S hS ≫ g3_proj X.J (r + 1) j.succ =
      snd A.X (g32c_B X S hS) ≫ cfd_proj r (g32c_parts X S hS) j ≫
        (X.part (S j) (hS j)).incl) ∧
    g32c_proj X S hS ≫ fst A.X (g32c_B X S hS) =
      g3_proj X.J (r + 1) 0 ≫ X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA) ∧
    (∀ j : Fin r, g32c_proj X S hS ≫ snd A.X (g32c_B X S hS) ≫
        cfd_proj r (g32c_parts X S hS) j =
      g3_proj X.J (r + 1) j.succ ≫ (X.part (S j) (hS j)).proj ≫
        𝟙 (g32c_parts X S hS j) ^ (g32c_N X S hS / (X.part (S j) (hS j)).N)) :=
  g32c_realization_aux X S hS

example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    IsMonHom (g32c_incl X S hS) ∧ IsMonHom (g32c_proj X S hS) ∧
    g32c_incl X S hS ≫ g3_proj X.J (r + 1) 0 = fst A.X (g32c_B X S hS) ≫ X.inclA ∧
    (∀ j : Fin r, g32c_incl X S hS ≫ g3_proj X.J (r + 1) j.succ =
      snd A.X (g32c_B X S hS) ≫ cfd_proj r (g32c_parts X S hS) j ≫
        (X.part (S j) (hS j)).incl) ∧
    g32c_proj X S hS ≫ fst A.X (g32c_B X S hS) =
      g3_proj X.J (r + 1) 0 ≫ X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA) ∧
    (∀ j : Fin r, g32c_proj X S hS ≫ snd A.X (g32c_B X S hS) ≫
        cfd_proj r (g32c_parts X S hS) j =
      g3_proj X.J (r + 1) j.succ ≫ (X.part (S j) (hS j)).proj ≫
        𝟙 (g32c_parts X S hS j) ^ (g32c_N X S hS / (X.part (S j) (hS j)).N)) :=
  g32c_realization X S hS

/-- **The retraction identities.** `N₀ > 0`, `ι₀ ≫ π = [N₀]` on `A_ρ × B`, and in cohomology
`ι₀^* ∘ π^* = N₀ⁿ` on `H^n(A_ρ × B; ℚ)` for every `n`.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "Γ is algebraic" (`π ∘ ι₀ = [N₀]` and
`ι₀^* π^* Γ = [N₀]^* Γ = N₀^{deg Γ} Γ`); `spec_homPullback_comp`, `spec_homPullback_zpow_degree`. -/
theorem g32c_retraction (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    0 < g32c_N X S hS ∧
    g32c_incl X S hS ≫ g32c_proj X S hS = 𝟙 (A.X ⊗ g32c_B X S hS) ^ g32c_N X S hS ∧
    ∀ n, homPullback (g32c_incl X S hS) n ∘ₗ homPullback (g32c_proj X S hS) n =
      ((g32c_N X S hS : ℚ) ^ n) • LinearMap.id :=
  g32c_retraction_aux X S hS

example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    0 < g32c_N X S hS ∧
    g32c_incl X S hS ≫ g32c_proj X S hS = 𝟙 (A.X ⊗ g32c_B X S hS) ^ g32c_N X S hS ∧
    ∀ n, homPullback (g32c_incl X S hS) n ∘ₗ homPullback (g32c_proj X S hS) n =
      ((g32c_N X S hS : ℚ) ^ n) • LinearMap.id :=
  g32c_retraction X S hS

/-- Consequence: `π^*` is injective in every degree, so a class on `A_ρ × B` is recovered from its
pullback to `J^{r+1}`. -/
example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (n : ℕ) :
    Function.Injective (homPullback (g32c_proj X S hS) n) := by
  obtain ⟨hN, -, h⟩ := g32c_retraction X S hS
  intro x y hxy
  have hx := congrArg (homPullback (g32c_incl X S hS) n) hxy
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, h n] at hx
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hx
  exact smul_right_injective _ (pow_ne_zero n (Nat.cast_ne_zero.mpr hN.ne')) hx

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32ContractionDefs

/-! # Carriers for the second stage of the G32 contraction

The correspondence `cfd_corrAction` as a bilinear map and its complexification, the degree-one
map `H¹(A_ρ; ℂ) × ∏_j H¹(P_j; ℂ) → H¹(J; ℂ)^{r+1}` induced by the projection `π`, the class on
`B = ∏_j P_j` of an element of the exterior algebra of the factors' degree-one cohomology, and
the product of a family of factor elements in that exterior algebra. Every carrier is a
definition; none records an invariance, an algebraicity or a contraction. HC no distance; AV
milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

/-! ## The complexified correspondence -/

/-- The correspondence `ξ ↦ (x ↦ cfd_corrAction Y B d I c p q h ξ x)` as a `ℚ`-bilinear map
`H^{2c}(Y × B) × H^{2p}(B) → H^{2q}(Y)`.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "The contraction is nonzero"
(`Γ_*(Y) = pr_{2*}(pr_1^* Y ∪ Γ)`); Fulton, *Intersection Theory*, §16.1; `cfd_corrAction`. -/
def g32c_corrQ (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d) :
    HQ (Y ⊗ B) (2 * c) →ₗ[ℚ] HQ B (2 * p) →ₗ[ℚ] HQ Y (2 * q) :=
  (((cupProductOf (Y ⊗ B)).cup h).compl₂ (homPullback (snd Y B) (2 * p))).compr₂
    (cfd_projection Y B d I (2 * q))

set_option maxRecDepth 4000 in
example (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (ξ : HQ (Y ⊗ B) (2 * c)) (x : HQ B (2 * p)) :
    g32c_corrQ Y B d I c p q h ξ x = cfd_corrAction Y B d I c p q h ξ x := rfl

/-- The complexified correspondence
`ℂ ⊗ H^{2c}(Y × B) × ℂ ⊗ H^{2p}(B) → ℂ ⊗ H^{2q}(Y)`, the `ℂ`-bilinear extension of `g32c_corrQ`:
the base change of its uncurried map, precomposed with
`(ℂ ⊗ M) ⊗_ℂ (ℂ ⊗ N) ≅ ℂ ⊗ (M ⊗ N)`.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "The contraction is nonzero" (the
correspondence applied to the complex class `Γ`); Mathlib `LinearMap.baseChange`,
`TensorProduct.AlgebraTensorModule.distribBaseChange`. -/
def g32c_corrC (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d) :
    ℂ ⊗[ℚ] HQ (Y ⊗ B) (2 * c) →ₗ[ℂ] ℂ ⊗[ℚ] HQ B (2 * p) →ₗ[ℂ] ℂ ⊗[ℚ] HQ Y (2 * q) :=
  TensorProduct.curry ((TensorProduct.lift (g32c_corrQ Y B d I c p q h)).baseChange ℂ ∘ₗ
    (TensorProduct.AlgebraTensorModule.distribBaseChange ℚ ℂ (HQ (Y ⊗ B) (2 * c))
      (HQ B (2 * p))).symm.toLinearMap)

example (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (x : ℂ ⊗[ℚ] HQ B (2 * p)) :
    g32c_corrC Y B d I c p q h 0 x = 0 := by
  simp

set_option maxRecDepth 4000 in
/-- On rational classes the complexified correspondence is the rational one. -/
example (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (ξ : HQ (Y ⊗ B) (2 * c)) (x : HQ B (2 * p)) :
    g32c_corrC Y B d I c p q h ((1 : ℂ) ⊗ₜ ξ) ((1 : ℂ) ⊗ₜ x) =
      (1 : ℂ) ⊗ₜ cfd_corrAction Y B d I c p q h ξ x := by
  simp only [g32c_corrC, TensorProduct.curry_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, mul_one,
    LinearMap.baseChange_tmul, TensorProduct.lift.tmul]
  rfl

/-! ## The degree-one map of the projection `π` -/

variable {A : g32t_Sixfold}

/-- The map `H¹(A_ρ; ℂ) × ∏_j H¹(P_j; ℂ) → H¹(J; ℂ)^{r+1}` whose components are the pullbacks along
the factor maps of `π = g32c_proj`: `(projA ≫ [N₀/N_A])^*` on the coordinate `0` and
`(proj_j ≫ [N₀/N_j])^*` on the coordinate `j + 1`. Together with `g32p_powerOne` it computes `π^*`
on degree-one classes.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "Γ is algebraic" (`π^* Γ` on `J^{57}`);
`g32c_proj`, `g32p_powerOne`. -/
def g32c_lowerOne (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    ((ℂ ⊗[ℚ] HQ A.X 1) × ∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1) →ₗ[ℂ]
      (Fin (r + 1) → ℂ ⊗[ℚ] HQ X.J 1) :=
  LinearMap.pi (Fin.cases (motive := fun _ => ((ℂ ⊗[ℚ] HQ A.X 1) ×
      ∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1) →ₗ[ℂ] ℂ ⊗[ℚ] HQ X.J 1)
    ((homPullback (X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA)) 1).baseChange ℂ ∘ₗ
      LinearMap.fst ℂ _ _)
    fun j => (homPullback ((X.part (S j) (hS j)).proj ≫
        𝟙 (g32c_parts X S hS j) ^ (g32c_N X S hS / (X.part (S j) (hS j)).N)) 1).baseChange ℂ ∘ₗ
      LinearMap.proj j ∘ₗ LinearMap.snd ℂ _ _)

example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) : g32c_lowerOne X S hS 0 = 0 := map_zero _

/-! ## Classes on `B` -/

/-- The degree-one classes of `B = ∏_j P_j` from those of the factors: the sum of the complexified
pullbacks along the factor projections `cfd_proj`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §1.3; `cfd_oneMap`. -/
def g32c_oneB (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    (∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1) →ₗ[ℂ] ℂ ⊗[ℚ] HQ (g32c_B X S hS) 1 :=
  ∑ j, (homPullback (cfd_proj r (g32c_parts X S hS) j) 1).baseChange ℂ ∘ₗ LinearMap.proj j

example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) : g32c_oneB X S hS 0 = 0 := map_zero _

/-- The class in `H^n(B; ℂ)` of the degree-`n` part of an element of the exterior algebra of the
factors' degree-one cohomology: the exterior power of `g32c_oneB` followed by the cup map. For
the product of the complexified Schoen wedges `y_j` this is the class `Y = ⊠_j y_j` of G32.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "The contraction is nonzero"
(`Y = ⊠_i y_i^{⊠|n_i|}`); Birkenhake–Lange, Lemma 1.3.1. -/
def g32c_classB (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (n : ℕ)
    (x : ExteriorAlgebra ℂ (∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)) :
    ℂ ⊗[ℚ] HQ (g32c_B X S hS) n :=
  letI := (torusCohomology_cupProductOf (g32c_B X S hS)).finite
  ((cupProductOf (g32c_B X S hS)).cupWedgeMap n).baseChange ℂ
    ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv n).symm
      (exteriorPower.map n (g32c_oneB X S hS)
        (DirectSum.decompose (fun i : ℕ => ⋀[ℂ]^i _) x n)))

example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (n : ℕ) : g32c_classB X S hS n 0 = 0 := by
  simp [g32c_classB]

/-- The product `⊠_j x_j` in the exterior algebra of `∏_j N_j` of a family `x_j ∈ ⋀ N_j`, in the
order of the factors; `g32c_gammaAbs w x` is `w` times its image under the second inclusion.
Source: G32 v0.16, proof of Proposition 4.6, paragraphs "The correspondence" and "The
contraction is nonzero" (`⊠_i`). -/
def g32c_prodAbs {r : ℕ} {N : Fin r → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)]
    (x : ∀ j, ExteriorAlgebra ℂ (N j)) : ExteriorAlgebra ℂ (∀ j, N j) :=
  (List.ofFn fun j => ExteriorAlgebra.map (LinearMap.single ℂ N j) (x j)).prod

example {N : Fin 0 → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)]
    (x : ∀ j, ExteriorAlgebra ℂ (N j)) : g32c_prodAbs x = 1 := by
  simp [g32c_prodAbs]

end HodgeLean.Foundations.Program

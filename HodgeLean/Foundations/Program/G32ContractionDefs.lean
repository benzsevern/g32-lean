import HodgeLean.Foundations.Program.G32PropFourSixDefs
import HodgeLean.Foundations.Program.CycleFoundationsFinite

/-! # Carriers for the first stage of the G32 contraction

The product `A_ρ × B`, `B = ∏_j P_j`, of a realized fibre and supplier parts, its maps to and from
the power `J(C)^{r+1}`, the centralizer `U` of `G` in the symplectic group of `H¹(J; ℂ)`, its
action on the cohomology of each factor and on the multiplicity spaces, the complementary
determinant lines, and the tensor `Γ` in the exterior algebra of the degree-one cohomology of the
factors, with its class on the product. Every carrier is a definition; none records an invariance,
an algebraicity or a contraction. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

/-! ## Products and powers -/

/-- The map `∏_j F_j ⟶ J^r` with components `ι_j`, factor by factor on the iterated products.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "Γ is algebraic" (the inclusions
`X' ↪ J(C)`, giving `ι₀`); Mathlib `MonoidalCategory.tensorHom`. -/
def g32c_lift (J : Over (Spec ↧ℂ)) :
    ∀ (r : ℕ) (F : Fin r → Over (Spec ↧ℂ)), (∀ i, F i ⟶ J) → (cfd_product r F ⟶ g3_power J r)
  | 0, _, _ => 𝟙 _
  | r + 1, F, f => f 0 ⊗ₘ g32c_lift J r (fun i => F i.succ) (fun i => f i.succ)

example (J : Over (Spec ↧ℂ)) (F : Fin 0 → Over (Spec ↧ℂ)) (f : ∀ i, F i ⟶ J) :
    g32c_lift J 0 F f = 𝟙 _ := rfl

/-- The map `J^r ⟶ ∏_j F_j` with components `p_j`, factor by factor on the iterated products.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "Γ is algebraic" (the homomorphisms
`N₀ e_{X'} : J(C) → X'`, giving `π`); Mathlib `MonoidalCategory.tensorHom`. -/
def g32c_lower (J : Over (Spec ↧ℂ)) :
    ∀ (r : ℕ) (F : Fin r → Over (Spec ↧ℂ)), (∀ i, J ⟶ F i) → (g3_power J r ⟶ cfd_product r F)
  | 0, _, _ => 𝟙 _
  | r + 1, F, p => p 0 ⊗ₘ g32c_lower J r (fun i => F i.succ) (fun i => p i.succ)

example (J : Over (Spec ↧ℂ)) (F : Fin 1 → Over (Spec ↧ℂ)) (p : ∀ i, J ⟶ F i) :
    g32c_lower J 1 F p = p 0 ⊗ₘ 𝟙 _ := rfl

/-! ## The product of a realized fibre with supplier parts -/

variable {A : g32t_Sixfold}

/-- The supplier parts `P_j = P_{χ_j}` of a list of admissible suppliers (repetitions allowed, so
that `P_i^{|n_i|}` is a list with `|n_i|` equal entries).
Source: G32 v0.16, proof of Proposition 4.6 (`B = ∏_i P_i^{|n_i|}`). -/
abbrev g32c_parts (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (j : Fin r) : Over (Spec ↧ℂ) :=
  (X.part (S j) (hS j)).P

example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (j : Fin r) : GrpObj (g32c_parts X S hS j) :=
  inferInstance

/-- The product `B = ∏_j P_j` of the supplier parts, an abelian variety.
Source: G32 v0.16, proof of Proposition 4.6 (`B = ∏_i P_i^{|n_i|}`); `cfd_product`. -/
abbrev g32c_B (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) : Over (Spec ↧ℂ) :=
  cfd_product r (g32c_parts X S hS)

example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    IsProjective (A.X ⊗ g32c_B X S hS).hom := inferInstance

/-- The common retraction degree `N₀ = N_A · ∏_j N_j`.
Source: G32 v0.16, proof of Proposition 4.6 ("choose one integer `N₀` for all of them"). -/
def g32c_N (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) : ℕ :=
  X.NA * ∏ j, (X.part (S j) (hS j)).N

example (X : g32p_Cover A) (S : Fin 0 → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    g32c_N X S hS = X.NA := by simp [g32c_N]

/-- The inclusion `ι₀ : A_ρ × B ⟶ J^{r+1}`, `inclA` on the first factor and the part inclusions
on the others.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "Γ is algebraic" (`ι₀`). -/
def g32c_incl (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) : A.X ⊗ g32c_B X S hS ⟶ g3_power X.J (r + 1) :=
  X.inclA ⊗ₘ g32c_lift X.J r (g32c_parts X S hS) (fun j => (X.part (S j) (hS j)).incl)

example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    g32c_incl X S hS = X.inclA ⊗ₘ g32c_lift X.J r (g32c_parts X S hS)
      (fun j => (X.part (S j) (hS j)).incl) := rfl

/-- The projection `π : J^{r+1} ⟶ A_ρ × B`: on each factor the given projection followed by
multiplication by `N₀ / N`, so that every factor has the retraction degree `N₀`.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "Γ is algebraic" (`π`, with
`π ∘ ι₀ = [N₀]`). -/
def g32c_proj (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) : g3_power X.J (r + 1) ⟶ A.X ⊗ g32c_B X S hS :=
  (X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA)) ⊗ₘ
    g32c_lower X.J r (g32c_parts X S hS) (fun j => (X.part (S j) (hS j)).proj ≫
      𝟙 (g32c_parts X S hS j) ^ (g32c_N X S hS / (X.part (S j) (hS j)).N))

example (X : g32p_Cover A) (S : Fin 0 → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    g32c_proj X S hS = (X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA)) ⊗ₘ 𝟙 _ := rfl

/-! ## The centralizer and its actions -/

/-- The complex points of the centralizer `U` of `G` in the symplectic group of `H¹(J)`:
invertible maps of `H¹(J; ℂ)` commuting with the pullback of every `g ∈ G` and fixing the
polarization in `⋀² H¹(J; ℂ)`.
Source: G32 v0.16, Subsection 4.2 ("Let `U` be the centralizer of `G` in the symplectic group of
`(H¹(C, ℚ), E)`; we only need its complex points"). -/
def g32c_U (X : g32p_Cover A) : Set (Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) :=
  {u | IsUnit u ∧
    (∀ g, u ∘ₗ (homPullback (X.aut g) 1).baseChange ℂ =
      (homPullback (X.aut g) 1).baseChange ℂ ∘ₗ u) ∧
    exteriorPower.map 2 u (HodgeBlocks.complexifyWedge 2
      (polarizationVec (torusCohomology_cupProductOf X.J) X.pol)) =
      HodgeBlocks.complexifyWedge 2 (polarizationVec (torusCohomology_cupProductOf X.J) X.pol)}

/-- Milne's group is contained in `U`: every `aut g` is an endomorphism. -/
example (X : g32p_Cover A) : g32p_lefschetz X.J X.pol ⊆ g32c_U X :=
  fun _ hu => ⟨hu.1, fun g => hu.2.1 (X.aut g) (X.aut_hom g), hu.2.2⟩

/-- `-1 ∈ U`: invariance under `U` is a genuine condition, killing every odd tensor degree. -/
example (X : g32p_Cover A) : -1 ∈ g32c_U X := by
  have h2 : exteriorPower.map 2 (-1 : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
      LinearMap.id_apply]
    have hv : (⇑(-1 : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) ∘ v) = fun i => (-1 : ℂ) • v i := by
      funext i
      simp
    rw [hv, AlternatingMap.map_smul_univ]
    simp
  refine ⟨isUnit_one.neg, fun g => LinearMap.ext fun x => by simp, ?_⟩
  rw [h2, LinearMap.id_apply]

/-- The action induced on `H¹(P; ℂ)` of a factor `P` with `incl ≫ proj = [N]`:
`N⁻¹ · incl^* ∘ u ∘ proj^*`. When `u` preserves the image of `proj^*`, this is `u` transported
along the injection `proj^*`.
Source: G32 v0.16, proof of Proposition 4.6 (`U` acts on the factors through the maps built from
`ℚ[G]`). -/
def g32c_restrict {P J : Over (Spec ↧ℂ)} [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (incl : P ⟶ J) (proj : J ⟶ P)
    (N : ℕ) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) : Module.End ℂ (ℂ ⊗[ℚ] HQ P 1) :=
  (N : ℂ)⁻¹ • ((homPullback incl 1).baseChange ℂ ∘ₗ u ∘ₗ (homPullback proj 1).baseChange ℂ)

example {P J : Over (Spec ↧ℂ)} [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (incl : P ⟶ J) (proj : J ⟶ P)
    (N : ℕ) : g32c_restrict incl proj N 0 = 0 := by
  simp [g32c_restrict]

/-- The multiplicity space `M_τ = Hom_G(τ, H¹(J; ℂ))`, for `G` acting by pullback.
Source: G32 v0.16, Subsection 4.2 (`H¹(C, ℂ) = ⊕_τ τ ⊗ M_τ`). -/
def g32c_mult (X : g32p_Cover A) (τ : FDRep ℂ g32p_G) :
    Submodule ℂ (τ →ₗ[ℂ] ℂ ⊗[ℚ] HQ X.J 1) where
  carrier := {φ | ∀ g, φ ∘ₗ τ.ρ g = (homPullback (X.aut g) 1).baseChange ℂ ∘ₗ φ}
  add_mem' {φ ψ} hφ hψ g := by
    rw [LinearMap.add_comp, hφ g, hψ g, LinearMap.comp_add]
  zero_mem' g := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  smul_mem' c φ hφ g := by
    rw [LinearMap.smul_comp, hφ g, LinearMap.comp_smul]

example (X : g32p_Cover A) (τ : FDRep ℂ g32p_G) : (0 : τ →ₗ[ℂ] _) ∈ g32c_mult X τ :=
  Submodule.zero_mem _

/-- The action of `u ∈ U` on `M_τ` by composition.
Source: G32 v0.16, Subsection 4.2 (`U(ℂ)` acts on `M_τ`, giving the factors `GL(M_τ)`,
`O(M_τ)`, `Sp(M_τ)`). -/
def g32c_multAct (X : g32p_Cover A) (τ : FDRep ℂ g32p_G) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1))
    (hu : u ∈ g32c_U X) : Module.End ℂ (g32c_mult X τ) :=
  (LinearMap.compRight ℂ u).restrict fun φ hφ g => by
    change (u ∘ₗ φ) ∘ₗ τ.ρ g = _ ∘ₗ (u ∘ₗ φ)
    rw [LinearMap.comp_assoc, hφ g, ← LinearMap.comp_assoc, hu.2.1 g, LinearMap.comp_assoc]

/-- The character `e_τ(u) = det(u | M_τ)` of `U`; for a pair `(τ, τ̄)` it is the coordinate
character of `T`, and for a quaternionic `τ` it is the sign of `u` in `O(M_τ)`.
Source: G32 v0.16, Subsection 4.2 (the character group `X*(T) = ℤ^{pairs} ⊕ (ℤ/2)^{quat}`). -/
def g32c_char (X : g32p_Cover A) (τ : FDRep ℂ g32p_G) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1))
    (hu : u ∈ g32c_U X) : ℂ :=
  LinearMap.det (g32c_multAct X τ u hu)

example (X : g32p_Cover A) (τ : FDRep ℂ g32p_G) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1))
    (hu : u ∈ g32c_U X) : g32c_char X τ u hu = LinearMap.det (g32c_multAct X τ u hu) := rfl

/-- The character of `U` with coordinates `a ∈ ℤ^I ⊕ (ℤ/2)^K` for an enumeration `τ` of the
pairs and `θ` of the quaternionic representations: `∏_i e_{τ_i}^{a_i} ∏_q e_{θ_q}^{a_q}`.
Source: G32 v0.16, Subsection 4.2 (characters of `T`). -/
def g32c_charOf (X : g32p_Cover A) {I K : Type*} [Fintype I] [Fintype K]
    (τ : I → FDRep ℂ g32p_G) (θ : K → FDRep ℂ g32p_G) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1))
    (hu : u ∈ g32c_U X) (a : (I → ℤ) × (K → ZMod 2)) : ℂ :=
  (∏ i, g32c_char X (τ i) u hu ^ a.1 i) * ∏ q, g32c_char X (θ q) u hu ^ (a.2 q).val

example (X : g32p_Cover A) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_charOf X (I := Empty) (K := Empty) Empty.elim Empty.elim u hu 0 = 1 := by
  simp [g32c_charOf]

/-- An enumeration of the pairs `(τ_j, τ̄_j)` of non-self-dual irreducible representations and of
the quaternionic irreducible representations `θ_j` with positive Chevalley–Weil multiplicity:
pairwise non-isomorphic and covering every such representation. These are the clauses of the
enumeration in `g32p_character_comparison` (on `spec/p46`), for arbitrary index types.
Source: G32 v0.16, Subsection 4.2 and Appendix B ("The vectors"). -/
def g32c_Enumeration {I K : Type*} (τ τbar : I → FDRep ℂ g32p_G) (θ : K → FDRep ℂ g32p_G) :
    Prop :=
  (∀ j, Simple (τ j) ∧ Simple (τbar j) ∧ ¬ g32p_SelfDual (τ j) ∧
    (∀ g, (τbar j).character g = star ((τ j).character g)) ∧ 0 < g32p_cwMult (τ j)) ∧
  (∀ j, Simple (θ j) ∧ g32p_Quaternionic (θ j) ∧ 0 < g32p_cwMult (θ j)) ∧
  (∀ j k, j ≠ k → IsEmpty (τ j ≅ τ k) ∧ IsEmpty (τ j ≅ τbar k)) ∧
  (∀ j k, j ≠ k → IsEmpty (θ j ≅ θ k)) ∧
  (∀ σ : FDRep ℂ g32p_G, Simple σ → 0 < g32p_cwMult σ →
    (¬ g32p_SelfDual σ → ∃ j, Nonempty (σ ≅ τ j) ∨ Nonempty (σ ≅ τbar j)) ∧
    (g32p_Quaternionic σ → ∃ j, Nonempty (σ ≅ θ j)))

example {I K : Type*} (τ τbar : I → FDRep ℂ g32p_G) (θ : K → FDRep ℂ g32p_G)
    (h : g32c_Enumeration τ τbar θ) (j : I) : ¬ g32p_SelfDual (τ j) := (h.1 j).2.2.1

/-! ## Complementary determinant lines -/

/-- The degree-`n` wedges of the sum of the eigenspaces of the embeddings `s ≠ t`. In degree
`h (φ(m) - 1)` this is the line `det(⊕_{s ≠ t} V_s)`, spanned by `Z = ∏_{s ≠ t} z_s`.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "The correspondence" (`Z_i`). -/
def g32c_coLine {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) (n : ℕ) :
    Submodule ℂ (⋀[ℂ]^n (ℂ ⊗[ℚ] V)) :=
  LinearMap.range (exteriorPower.map n (⨆ (s) (_ : s ≠ t), cyc_eigenspace e s).subtype)

example {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) (n : ℕ) :
    (0 : ⋀[ℂ]^n (ℂ ⊗[ℚ] V)) ∈ g32c_coLine e t n := Submodule.zero_mem _

/-! ## The tensor `Γ` -/

/-- The tensor `Γ = w ⊠ ⊠_j Z_j` in the exterior algebra of `M × ∏_j N_j`, the product of the
images of `w ∈ ⋀ M` and of each `Z_j ∈ ⋀ N_j`, in the order of the factors.
Source: G32 v0.16, proof of Proposition 4.6, paragraph "The correspondence" (`Γ`). -/
def g32c_gammaAbs {M : Type*} [AddCommGroup M] [Module ℂ M] {r : ℕ} {N : Fin r → Type*}
    [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)] (w : ExteriorAlgebra ℂ M)
    (Z : ∀ j, ExteriorAlgebra ℂ (N j)) : ExteriorAlgebra ℂ (M × ∀ j, N j) :=
  ExteriorAlgebra.map (LinearMap.inl ℂ M (∀ j, N j)) w *
    (List.ofFn fun j => ExteriorAlgebra.map
      (LinearMap.inr ℂ M (∀ j, N j) ∘ₗ LinearMap.single ℂ N j) (Z j)).prod

example {M : Type*} [AddCommGroup M] [Module ℂ M] {N : Fin 0 → Type*}
    [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)] (w : ExteriorAlgebra ℂ M)
    (Z : ∀ j, ExteriorAlgebra ℂ (N j)) :
    g32c_gammaAbs w Z = ExteriorAlgebra.map (LinearMap.inl ℂ M (∀ j, N j)) w := by
  simp [g32c_gammaAbs]

/-- The action of a family of endomorphisms of the factors on the exterior algebra of their sum.
Source: G32 v0.16, proof of Proposition 4.6 (the action of `U` on `H*(B × A_ρ) = ⋀ H¹`). -/
def g32c_factorAction {M : Type*} [AddCommGroup M] [Module ℂ M] {r : ℕ} {N : Fin r → Type*}
    [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)] (uM : Module.End ℂ M)
    (uN : ∀ j, Module.End ℂ (N j)) : ExteriorAlgebra ℂ (M × ∀ j, N j) →ₐ[ℂ]
      ExteriorAlgebra ℂ (M × ∀ j, N j) :=
  ExteriorAlgebra.map (LinearMap.prodMap uM (LinearMap.pi fun j => uN j ∘ₗ LinearMap.proj j))

example {M : Type*} [AddCommGroup M] [Module ℂ M] {r : ℕ} {N : Fin r → Type*}
    [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)] (x : ExteriorAlgebra ℂ (M × ∀ j, N j)) :
    g32c_factorAction (N := N) LinearMap.id (fun _ => LinearMap.id) x = x := by
  simp [g32c_factorAction]

/-- The degree-one classes of `A_ρ × B` from those of the factors: the sum of the pullbacks along
the projections to `A_ρ` and to each `P_j`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §1.3; `cfd_oneMap`. -/
def g32c_oneC (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    ((ℂ ⊗[ℚ] HQ A.X 1) × ∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1) →ₗ[ℂ]
      ℂ ⊗[ℚ] HQ (A.X ⊗ g32c_B X S hS) 1 :=
  (homPullback (fst A.X (g32c_B X S hS)) 1).baseChange ℂ ∘ₗ LinearMap.fst ℂ _ _ +
    ∑ j, (homPullback (snd A.X (g32c_B X S hS) ≫ cfd_proj r (g32c_parts X S hS) j) 1).baseChange ℂ
      ∘ₗ LinearMap.proj j ∘ₗ LinearMap.snd ℂ _ _

example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) : g32c_oneC X S hS 0 = 0 := map_zero _

/-- The class in `H^n(A_ρ × B; ℂ)` of the degree-`n` part of an element of the exterior algebra of
the factors' degree-one cohomology: the exterior power of `g32c_oneC` followed by the cup map.
For `x = g32c_gammaAbs w Z` this is the class `Γ` of G32.
Source: G32 v0.16, proof of Proposition 4.6 (`Γ ∈ H*(B × A_ρ, ℂ)`); Birkenhake–Lange, Lemma
1.3.1. -/
def g32c_class (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (n : ℕ)
    (x : ExteriorAlgebra ℂ ((ℂ ⊗[ℚ] HQ A.X 1) × ∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)) :
    ℂ ⊗[ℚ] HQ (A.X ⊗ g32c_B X S hS) n :=
  letI := (torusCohomology_cupProductOf (A.X ⊗ g32c_B X S hS)).finite
  ((cupProductOf (A.X ⊗ g32c_B X S hS)).cupWedgeMap n).baseChange ℂ
    ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv n).symm
      (exteriorPower.map n (g32c_oneC X S hS)
        (DirectSum.decompose (fun i : ℕ => ⋀[ℂ]^i _) x n)))

example (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (n : ℕ) : g32c_class X S hS n 0 = 0 := by
  simp [g32c_class]

end HodgeLean.Foundations.Program

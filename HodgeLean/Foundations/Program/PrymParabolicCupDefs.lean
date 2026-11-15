import HodgeLean.Foundations.Program.PrymParabolicComparison

/-! # Definitions for stage H4, algebraic part: the cup form on `H¹_σ` and a `K`-form of `σ`

On the lifted complex `X̃(g)` of stage H3a (`PrymParabolicComparisonDefs`): the cellular cup
product of `1`-cochains evaluated on the orientation chain, as a sesquilinear form; its version on
the equivariant cohomology `H¹_σ = hg_eqH1 σ g`, read on representatives chosen by a linear
section; and the linear map `V_par → H¹_σ` induced by the explicit Shapiro map. Then a `K`-form of
the defining representation of `b4b_Group` over `K = ℚ(√−3)`: the matrices of the printed
generators at `ζ = (−1 + √−3)/2` generate a monoid that `hp_embed` carries onto `b4b_Group`.

Nothing here compares the cup form with an intersection form on `H₁` of a cover, or `H¹_σ` with a
Prym lattice (stages H3b, H4 geometric part, H5). HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

/-! ## The cup form on cochains and on `H¹_σ` -/

/-- The cellular cup product of two `1`-cochains with the fibre form
`h(u, v) = star u ⬝ᵥ (H *ᵥ v)`, evaluated on the orientation chain `Σ_x Σ_i (A_i(x) − B_i(x))`:
`α, β ↦ hg_fundEval (hg_cup g H α β)`, conjugate-linear in `α` and linear in `β`.
Source: Hatcher, *Algebraic Topology*, §3.2 (cup product on a Δ-complex) and §3.3 (evaluation on
the fundamental class); `hg_cup`, `hg_fundEval`. -/
def hg4_cupForm {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] {r : ℕ} (g : Fin r → G) (H : Matrix ι ι K) :
    (hg_Edge G r → ι → K) →ₗ⋆[K] (hg_Edge G r → ι → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K)
    (fun α β => hg_fundEval (hg_cup g H α β))
    (fun α α' β => by
      simp only [hg_fundEval, hg_cup, Pi.add_apply, star_add, add_dotProduct,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      abel)
    (fun t α β => by
      simp only [hg_fundEval, hg_cup, Pi.smul_apply, star_smul, smul_dotProduct,
        starRingEnd_apply, smul_eq_mul, Finset.mul_sum, mul_sub])
    (fun α β β' => by
      simp only [hg_fundEval, hg_cup, Pi.add_apply, Matrix.mulVec_add, dotProduct_add,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      abel)
    (fun t α β => by
      simp only [hg_fundEval, hg_cup, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul,
        RingHom.id_apply, smul_eq_mul, Finset.mul_sum, mul_sub])

example {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] {r : ℕ} (g : Fin r → G) (H : Matrix ι ι K)
    (α β : hg_Edge G r → ι → K) :
    hg4_cupForm g H α β = hg_fundEval (hg_cup g H α β) := rfl

/-- A linear section `H¹_σ → C¹_σ ∩ ker δ¹` of the quotient map: the inverse of the quotient map
restricted to a chosen complement of the equivariant coboundaries.
Source: linear algebra over a field (`Submodule.exists_isCompl`,
`Submodule.quotientEquivOfIsCompl`); the same construction as `pc_lift`. -/
def hg4_lift {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    hg_eqH1 σ g →ₗ[K] hg_eqCocycles σ g :=
  let p := (hg_eqCoboundaries σ g).comap (hg_eqCocycles σ g).subtype
  (Classical.choose (Submodule.exists_isCompl p)).subtype ∘ₗ
    (Submodule.quotientEquivOfIsCompl p _
      (Classical.choose_spec (Submodule.exists_isCompl p))).toLinearMap

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) (x : hg_eqH1 σ g) :
    Submodule.Quotient.mk (hg4_lift σ g x) = x :=
  Submodule.mk_quotientEquivOfIsCompl_apply
    (Classical.choose_spec (Submodule.exists_isCompl _)) x

/-- The cup form on `H¹_σ`: `hg4_cupForm` evaluated on the representatives chosen by `hg4_lift`.
It is sesquilinear by construction; that it does not depend on the representatives under
product one is statement 3 (`hg4_cupH1_mk`).
Source: Hatcher, §3.2 (the cup product descends to cohomology); `hg4_cupForm`. -/
def hg4_cupH1 {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (H : Matrix ι ι K) : hg_eqH1 σ g →ₗ⋆[K] hg_eqH1 σ g →ₗ[K] K :=
  ((hg4_cupForm g H).comp ((hg_eqCocycles σ g).subtype ∘ₗ hg4_lift σ g)).compl₂
    ((hg_eqCocycles σ g).subtype ∘ₗ hg4_lift σ g)

example {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (H : Matrix ι ι K) (x y : hg_eqH1 σ g) :
    hg4_cupH1 σ g H x y = hg4_cupForm g H (hg4_lift σ g x) (hg4_lift σ g y) := rfl

/-! ## The Shapiro map on classes -/

/-- The explicit Shapiro map on parameters in `Z`, with values in the equivariant cocycles
(`hg_shapiro_cocycle` and the equivariance of `hg_shapiroCochain`).
Source: G32 v0.16, Lemma 6.2; Brown, *Cohomology of Groups*, Chapter III, §5; `hg_shapiroCochain`. -/
def hg4_shapiroZ {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    pc_Z (pc_tuple σ g) →ₗ[K] hg_eqCocycles σ g :=
  LinearMap.codRestrict (hg_eqCocycles σ g)
    (hg_shapiroCochain σ g ∘ₗ (pc_Z (pc_tuple σ g)).subtype) fun a => by
      refine ⟨fun h ε => ?_, hg_shapiro_cocycle σ g a a.2⟩
      rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
        simp [hg_shapiroCochain, hg_actEdge, map_mul, Matrix.mulVec_mulVec, Matrix.mulVec_neg,
          Matrix.mul_assoc]

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (a : pc_Z (pc_tuple σ g)) :
    (hg4_shapiroZ σ g a : hg_Edge G r → ι → K) = hg_shapiroCochain σ g a := rfl

/-- The map `V_par(pc_tuple σ g) → H¹_σ(X̃(g))` induced by the Shapiro map; the trivial part goes
to equivariant coboundaries (`hg_shapiro_coboundary_iff`). Defined for every tuple.
Source: G32 v0.16, Lemma 6.2 and proof of Proposition 6.3; Brown, Chapter III, §5. -/
def hg4_shapiroH1 {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    pc_Vpar (pc_tuple σ g) →ₗ[K] hg_eqH1 σ g :=
  Submodule.mapQ _ _ (hg4_shapiroZ σ g) fun a ha =>
    (hg_shapiro_coboundary_iff σ g a).2 ha

example {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (a : pc_Z (pc_tuple σ g)) :
    hg4_shapiroH1 σ g (Submodule.Quotient.mk a) = Submodule.Quotient.mk (hg4_shapiroZ σ g a) :=
  rfl

/-! ## A `K`-form of the defining representation of `b4b_Group` -/

/-- The matrices of a printed generator over `K` and over `ℂ` correspond under `hp_embed`.
Source: `g32R1`, `g32R2`, `g32X`, `g32Y` (entries polynomial in `ω` with rational coefficients);
`hp_embed_zeta`. -/
theorem hg4_gen_map :
    hp_embed.mapMatrix (HodgeLean.Papers.g32R1 pc_zeta) =
        HodgeLean.Papers.g32R1 HodgeLean.Papers.g32h_omega ∧
      hp_embed.mapMatrix (HodgeLean.Papers.g32R2 pc_zeta) =
        HodgeLean.Papers.g32R2 HodgeLean.Papers.g32h_omega ∧
      hp_embed.mapMatrix (HodgeLean.Papers.g32X pc_zeta) =
        HodgeLean.Papers.g32X HodgeLean.Papers.g32h_omega ∧
      hp_embed.mapMatrix (HodgeLean.Papers.g32Y pc_zeta) =
        HodgeLean.Papers.g32Y HodgeLean.Papers.g32h_omega := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HodgeLean.Papers.g32R1, HodgeLean.Papers.g32R2, HodgeLean.Papers.g32X,
        HodgeLean.Papers.g32Y, map_div₀, map_ofNat, hp_embed_zeta]

/-- The entrywise map `hp_embed` on `4 × 4` matrices, as a monoid map.
Source: `RingHom.mapMatrix`; `hp_embed`. -/
def hg4_embedMatrix : Matrix (Fin 4) (Fin 4) hp_K →* Matrix (Fin 4) (Fin 4) ℂ :=
  (hp_embed.mapMatrix : Matrix (Fin 4) (Fin 4) hp_K →+* Matrix (Fin 4) (Fin 4) ℂ).toMonoidHom

example (A : Matrix (Fin 4) (Fin 4) hp_K) : hg4_embedMatrix A = A.map hp_embed := rfl

/-- The monoid generated over `K` by the printed `r₁, r₂, x, y` at `ζ`.
Source: G32 v0.16, Appendix A (`G = ⟨r₁, r₂, x, y⟩ ⊂ GL₄(K)`, `K = ℚ(√−3)`); `g32h_G`. -/
def hg4_groupK : Submonoid (Matrix (Fin 4) (Fin 4) hp_K) :=
  Submonoid.closure {HodgeLean.Papers.g32R1 pc_zeta, HodgeLean.Papers.g32R2 pc_zeta,
    HodgeLean.Papers.g32X pc_zeta, HodgeLean.Papers.g32Y pc_zeta}

example : HodgeLean.Papers.g32X pc_zeta ∈ hg4_groupK := Submonoid.subset_closure (by simp)

/-- `hp_embed` carries the `K`-generated monoid onto `b4b_Group`.
Source: `Submonoid.map_closure`; `hg4_gen_map`. -/
theorem hg4_groupK_map :
    hg4_groupK.map hg4_embedMatrix =
      HodgeLean.Papers.g32h_G := by
  obtain ⟨h1, h2, h3, h4⟩ := hg4_gen_map
  rw [hg4_groupK, MonoidHom.map_mclosure]
  simp only [Set.image_insert_eq, Set.image_singleton]
  exact congrArg Submonoid.closure (by
    simp only [hg4_embedMatrix, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, h1, h2, h3, h4])

/-- The entrywise map `hp_embed` on `K`-matrices is injective.
Source: a ring map out of a field is injective. -/
theorem hg4_embedMatrix_injective : Function.Injective hg4_embedMatrix :=
  fun _ _ h => Matrix.ext fun i j => hp_embed.injective (congrFun (congrFun h i) j)

/-- The `K`-form of the defining representation: `b4b_Group ≃* hg4_groupK` (inverse of the
entrywise `hp_embed`), followed by the inclusion into `K`-matrices.
Source: G32 v0.16, Appendix A (the representation is defined over `K`); `hg4_groupK_map`. -/
def hg4_sigmaK : b4b_Group →* Matrix (Fin 4) (Fin 4) hp_K :=
  hg4_groupK.subtype.comp
    ((Submonoid.equivMapOfInjective hg4_groupK hg4_embedMatrix hg4_embedMatrix_injective).trans
      (MulEquiv.submonoidCongr hg4_groupK_map)).symm.toMonoidHom

example : hg4_sigmaK 1 = 1 := map_one _

end HodgeLean.Foundations.Program

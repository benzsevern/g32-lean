import HodgeLean.Foundations.Program.PrymParabolicRealization
import HodgeLean.Foundations.Program.PrymParabolicCup
import HodgeLean.Foundations.Program.PrymVariationCentreScalar

/-! # Definitions for stage H5, first part: the saturated cellular lattice and its centre

For the G32 root `b4b_root` and the lifted complex `X̃(b4b_root)` of stages H3a–H3b:

- the B6-3b group-ring operators of a family of `ℤ`-linear maps indexed by `b4b_Group`: the
  primitive operator `Σ_h b4b_projectorCoeff h · ρ(h)` and the central operator
  `Σ_g [b4b_toMatrix g = ω·1] ρ(g)`, in the exact shapes of `b63l_homologyOperator` and
  `b63d_centre`;
- the saturation of `range hg2_projector` in cellular `H₁(X̃(b4b_root); ℤ)` (the cellular analogue
  of `b63l_parameterLattice`), the cellular central operator, the fact that it commutes with
  `hg2_projector` (a central element, with a body), its restriction to the saturated lattice, the
  operator `1 + 2Z` there and its rationalization;
- the vector-valued evaluation of a `1`-cochain with values in `ι → K` on an integral `1`-chain,
  and the scalar cup product of two coordinates of vector-valued cochains on the orientation chain.

Nothing here identifies cellular with singular homology, or the cup product with an intersection
form. HC no distance; AV milestone no distance.
-/

noncomputable section

open HodgeLean.Papers
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

/-! ## Group-ring operators of a family of maps -/

/-- The B6-3b primitive operator `Σ_h b4b_projectorCoeff h · ρ(h)` of a family of `ℤ`-linear maps
indexed by `b4b_Group`. For `ρ = hg2_H1act ℤ b4b_root` it is `hg2_projector`, and for the deck
action on singular `H₁` it is `b63l_homologyOperator`, both by definition.
Source: G32 v0.16, Definition 3.2; `b4b_projectorCoeff`, `b4_groupEnd`. -/
def hg6_projOf {M : Type*} [AddCommGroup M] [Module ℤ M] (ρ : b4b_Group → M →ₗ[ℤ] M) :
    M →ₗ[ℤ] M :=
  ∑ h : b4b_Group, b4b_projectorCoeff h • ρ h

example : hg6_projOf (hg2_H1act ℤ b4b_root) = hg2_projector := rfl

/-- The central operator `Σ_g [b4b_toMatrix g = ω·1] ρ(g)` of a family of `ℤ`-linear maps, in the
shape of `b63d_centre`. Exactly one `g` (`b63d_scalarElement`) satisfies the condition.
Source: G32 v0.16, §3.3 and Appendix A; `b63d_centre`. -/
def hg6_centreOf {M : Type*} [AddCommGroup M] [Module ℤ M] (ρ : b4b_Group → M →ₗ[ℤ] M) :
    M →ₗ[ℤ] M :=
  ∑ g : b4b_Group, if b4b_toMatrix g = g32h_omega • (1 : Matrix (Fin 4) (Fin 4) ℂ)
    then ρ g else 0

example {M : Type*} [AddCommGroup M] [Module ℤ M] :
    hg6_centreOf (fun _ => (0 : M →ₗ[ℤ] M)) = 0 := by
  simp [hg6_centreOf]

/-- An element whose matrix is a scalar is central in `b4b_Group` (`b4b_toMatrix` is injective).
-/
theorem hg6_scalar_comm (g h : b4b_Group)
    (hg : b4b_toMatrix g = g32h_omega • (1 : Matrix (Fin 4) (Fin 4) ℂ)) : g * h = h * g := by
  apply Subtype.val_injective
  change b4b_toMatrix (g * h) = b4b_toMatrix (h * g)
  rw [map_mul, map_mul, hg, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

example (h : b4b_Group) : b63d_scalarElement * h = h * b63d_scalarElement :=
  hg6_scalar_comm _ h b63d_scalarElement_matrix

/-! ## The saturated cellular lattice -/

/-- The saturated cellular lattice: the saturation of the image of the B6-3b projector in
cellular `H₁(X̃(b4b_root); ℤ)`, the cellular analogue of `b63l_parameterLattice` (which saturates
the image of the same operator on singular `H₁` of a fibre).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §12.2 (the lattice of an image abelian
subvariety is saturated); `b63l_saturation`, `hg2_projector`. -/
def hg6_cellLattice : Submodule ℤ (hg2_H1 ℤ b4b_root) :=
  b63l_saturation (LinearMap.range hg2_projector)

example : LinearMap.range hg2_projector ≤ hg6_cellLattice :=
  fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩

/-- The cellular central operator on `H₁(X̃(b4b_root); ℤ)`, the deck action of the central element
with matrix `ω·1`, in the shape of `b63d_centre`.
Source: G32 v0.16, §3.3 and Appendix A; `b63d_centre`. -/
def hg6_cellCentre : hg2_H1 ℤ b4b_root →ₗ[ℤ] hg2_H1 ℤ b4b_root :=
  hg6_centreOf (hg2_H1act ℤ b4b_root)

example : hg6_cellCentre 0 = 0 := map_zero _

/-- The central operator is the action of `b63d_scalarElement`, the unique element with matrix
`ω·1` (`b4b_toMatrix` is injective). -/
theorem hg6_centreOf_eq {M : Type*} [AddCommGroup M] [Module ℤ M]
    (ρ : b4b_Group → M →ₗ[ℤ] M) :
    hg6_centreOf ρ = ρ b63d_scalarElement := by
  classical
  have hiff : ∀ g : b4b_Group,
      b4b_toMatrix g = g32h_omega • (1 : Matrix (Fin 4) (Fin 4) ℂ) ↔ g = b63d_scalarElement :=
    fun g => ⟨fun h => Subtype.val_injective (h.trans b63d_scalarElement_matrix.symm),
      fun h => h ▸ b63d_scalarElement_matrix⟩
  unfold hg6_centreOf
  simp_rw [hiff]
  simp

example : hg6_cellCentre = hg2_H1act ℤ b4b_root b63d_scalarElement := hg6_centreOf_eq _

/-- The cellular central operator commutes with the projector: the element it acts by is central
(`hg6_scalar_comm`), and `h ↦ h_*` is multiplicative on `H₁` (`hg2_H1act_mul`). -/
theorem hg6_cellCentre_comm :
    hg6_cellCentre ∘ₗ hg2_projector = hg2_projector ∘ₗ hg6_cellCentre := by
  have hmul (h k : b4b_Group) (x : hg2_H1 ℤ b4b_root) :
      hg2_H1act ℤ b4b_root h (hg2_H1act ℤ b4b_root k x) = hg2_H1act ℤ b4b_root (h * k) x :=
    LinearMap.congr_fun (hg2_H1act_mul ℤ b4b_root h k) x
  apply LinearMap.ext
  intro x
  simp only [hg6_cellCentre, hg6_centreOf_eq, hg2_projector, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, hmul,
    hg6_scalar_comm _ _ b63d_scalarElement_matrix]

/-- The cellular central operator restricted to the saturated cellular lattice (it preserves the
image of the projector by `hg6_cellCentre_comm`, hence its saturation).
Source: G32 v0.16, §3.3; the cellular analogue of `b63d_centre_range`. -/
def hg6_cellCentreL : hg6_cellLattice →ₗ[ℤ] hg6_cellLattice :=
  hg6_cellCentre.restrict fun x hx => by
    obtain ⟨n, hn, y, hy⟩ := hx
    refine ⟨n, hn, hg6_cellCentre y, ?_⟩
    rw [← map_zsmul, ← hy]
    exact (LinearMap.congr_fun hg6_cellCentre_comm y).symm

example (x : hg6_cellLattice) : (hg6_cellCentreL x : hg2_H1 ℤ b4b_root) = hg6_cellCentre x :=
  rfl

/-- The integral operator `1 + 2Z` on the saturated cellular lattice, the cellular analogue of the
restriction of `b63d_operator`.
Source: G32 v0.16, §3.3 (the expression `1 + 2ω`); `b63d_operator`. -/
def hg6_cellOperator : hg6_cellLattice →ₗ[ℤ] hg6_cellLattice :=
  LinearMap.id + 2 • hg6_cellCentreL

example (x : hg6_cellLattice) : hg6_cellOperator x = x + 2 • hg6_cellCentreL x := rfl

/-- The rationalization of `1 + 2Z` on the saturated rational cellular lattice `ℚ ⊗ L`.
Source: Bourbaki, *Algebra*, Ch. II, §5 (extension of scalars); `hg6_cellOperator`. -/
def hg6_cellJ : (ℚ ⊗[ℤ] hg6_cellLattice) →ₗ[ℚ] (ℚ ⊗[ℤ] hg6_cellLattice) :=
  hg6_cellOperator.baseChange ℚ

example (q : ℚ) (x : hg6_cellLattice) : hg6_cellJ (q ⊗ₜ x) = q ⊗ₜ hg6_cellOperator x := rfl

/-! ## Vector-valued evaluation and the coordinate cup product -/

/-- The evaluation `⟨c, z⟩ = Σ_ε z(ε) c(ε) ∈ ι → K` of a `1`-cochain with values in `ι → K` on an
integral `1`-chain of the lifted complex (`hg2_pair` coordinatewise).
Source: Hatcher, *Algebraic Topology*, §3.1 (the evaluation map of the universal coefficient
theorem). -/
def hg6_pairVec {K : Type*} [Field K] {ι : Type*} {G : Type*} {r : ℕ}
    (c : hg_Edge G r → ι → K) (z : hg2_Edge G r →₀ ℤ) : ι → K :=
  z.sum fun ε n => (n : K) • c ε

example {K : Type*} [Field K] {ι : Type*} {G : Type*} {r : ℕ} (c : hg_Edge G r → ι → K)
    (z : hg2_Edge G r →₀ ℤ) (i : ι) :
    hg6_pairVec c z i = hg2_pair K (fun ε => c ε i) z := by
  simp [hg6_pairVec, hg2_pair, Finsupp.sum, Finset.sum_apply]

/-- The scalar cup product of the coordinates `i` and `j` of two vector-valued `1`-cochains,
evaluated on the orientation chain: `Σ_x Σ_i (κ(A_i(x)) − κ(B_i(x)))` for
`κ(τ) = star (α(face₂ τ) i) · β(face₀ τ) j`. Summed over `i = j` it is `hg4_cupForm g 1`.
Source: Hatcher, §3.2 (cup product on a Δ-complex) and §3.3; `hg_cup`, `hg_fundEval`. -/
def hg6_coordCup {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} {r : ℕ} (g : Fin r → G) (i j : ι) (α β : hg_Edge G r → ι → K) : K :=
  hg_fundEval fun τ => star (α (hg_face2 τ) i) * β (hg_face0 g τ) j

example {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (g : Fin r → G)
    (α β : hg_Edge G r → ι → K) :
    ∑ i, hg6_coordCup g i i α β = hg4_cupForm g 1 α β := by
  simp only [hg6_coordCup, hg4_cupForm, LinearMap.mk₂'ₛₗ_apply, hg_cup, hg_fundEval,
    Matrix.one_mulVec, dotProduct, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_sub_distrib]

end HodgeLean.Foundations.Program

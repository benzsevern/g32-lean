import HodgeLean.Foundations.Program.PrymFamilyB4Defs
import HodgeLean.Papers.PapersG32CertificatesDefs

/-! # Definitions for PC stages H2 and H6: parabolic cocycles of a monodromy tuple

The parameter model of the parabolic cohomology of a tuple `T₁, …, T_r` of matrices with
product one, with coefficients in the column-vector space `ι → K` on which `Tᵢ` acts on the
left (the local system of the tuple itself: neither its dual nor its conjugate), together with
the cup-product formula of G32 Lemma 6.2 and its descended pairing on the quotient. Then the G32
root tuple, six explicit parameter tuples for it, and the same root and tuples over
`K = ℚ(√−3)` with a complex embedding of `K`.

Nothing here identifies the quotient with the cohomology of a punctured sphere or of a cover
(stages H3–H5). HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

/-- `Q_i = T₁ ⋯ T_{i−1}` (index `i` of `Fin r` is the `(i+1)`-st puncture, so `Q` at `0` is `1`).
Source: G32 v0.16, before Lemma 6.2 ("Put `Q_i = T₁ ⋯ T_{i−1}`"). -/
def pc_Q {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (i : Fin r) : Matrix ι ι K :=
  (((List.finRange r).filter fun j => j < i).map T).prod

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin (r + 1) → Matrix ι ι K) : pc_Q T 0 = 1 := by
  simp [pc_Q]

/-- `c_i = (1 − T_i) a_i`, the value on the loop `ℓ_i` of the cocycle with parameters `a`.
Source: G32 v0.16, before Lemma 6.2. -/
def pc_c {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) (i : Fin r) : ι → K :=
  (1 - T i) *ᵥ a i

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (a : Fin r → ι → K) (i : Fin r) : pc_c (fun _ => 1) a i = 0 := by
  simp [pc_c]

/-- `F_i = Σ_{j<i} Q_j c_j`.
Source: G32 v0.16, before Lemma 6.2. -/
def pc_F {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) (i : Fin r) : ι → K :=
  ∑ j ∈ Finset.univ.filter (· < i), pc_Q T j *ᵥ pc_c T a j

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin (r + 1) → Matrix ι ι K) (a : Fin (r + 1) → ι → K) : pc_F T a 0 = 0 := by
  simp [pc_F]

/-- The product relation `a ↦ Σ_i Q_i (1 − T_i) a_i`, the value of the cocycle on
`ℓ₁ ⋯ ℓ_r`.
Source: G32 v0.16, before Lemma 6.2 ("`Σ_i Q_i(1 − T_i)a_i = 0`"). -/
def pc_relation {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : (Fin r → ι → K) →ₗ[K] (ι → K) where
  toFun a := ∑ i, pc_Q T i *ᵥ pc_c T a i
  map_add' a b := by
    simp only [pc_c, Pi.add_apply, Matrix.mulVec_add, Finset.sum_add_distrib]
  map_smul' t a := by
    simp only [pc_c, Pi.smul_apply, Matrix.mulVec_smul, Finset.smul_sum, RingHom.id_apply]

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (a : Fin r → ι → K) :
    pc_relation T a = ∑ i, pc_Q T i *ᵥ pc_c T a i := rfl

/-- The parameter space `Z`: the tuples `(a_i)` with `Σ_i Q_i (1 − T_i) a_i = 0`.
Source: G32 v0.16, before Lemma 6.2 and proof of Proposition 6.3. -/
def pc_Z {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : Submodule K (Fin r → ι → K) :=
  LinearMap.ker (pc_relation T)

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : (0 : Fin r → ι → K) ∈ pc_Z T :=
  Submodule.zero_mem _

/-- The constant tuples `(v, …, v)`: the parameters of the coboundary of `v`, whose value on
`ℓ_i` is `(1 − T_i) v`.
Source: G32 v0.16, Lemma 6.2 ("vanishes on coboundaries"); Brown, *Cohomology of Groups*,
Chapter IV, §2 (coboundaries). -/
def pc_coboundaries {K : Type*} [Field K] (ι : Type*) [Fintype ι] (r : ℕ) :
    Submodule K (Fin r → ι → K) :=
  LinearMap.range (LinearMap.pi fun _ : Fin r => (LinearMap.id : (ι → K) →ₗ[K] (ι → K)))

example {K : Type*} [Field K] (ι : Type*) [Fintype ι] (r : ℕ) (v : ι → K) :
    (fun _ : Fin r => v) ∈ pc_coboundaries (K := K) ι r :=
  ⟨v, rfl⟩

/-- The fixed space `ker(T_i − 1)` of one local monodromy.
Source: G32 v0.16, Proposition 3.1 (`c_τ(g) = rk(τ(g) − 1)`) and Lemma 6.2. -/
def pc_localFixed {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (i : Fin r) : Submodule K (ι → K) :=
  LinearMap.ker (Matrix.toLin' (T i - 1))

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (i : Fin r) : pc_localFixed (fun _ : Fin r => (1 : Matrix ι ι K)) i = ⊤ := by
  simp [pc_localFixed]

/-- The tuples with every `a_i ∈ ker(1 − T_i)`; they give the zero cocycle.
Source: G32 v0.16, Lemma 6.2 ("determined by the cocycle modulo `ker(1 − T_i)`"). -/
def pc_localPart {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : Submodule K (Fin r → ι → K) :=
  Submodule.pi Set.univ fun i => pc_localFixed T i

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : (0 : Fin r → ι → K) ∈ pc_localPart T :=
  Submodule.zero_mem _

/-- The subspace killed in passing from parameters to classes: coboundaries plus the tuples
in `Π_i ker(1 − T_i)`.
Source: G32 v0.16, proof of Proposition 6.3 ("its radical … is spanned by the tuples coming
from coboundaries and the tuples with every `a_i ∈ ker(1 − T_i)`"). -/
def pc_trivialPart {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : Submodule K (Fin r → ι → K) :=
  pc_coboundaries ι r ⊔ pc_localPart T

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : pc_localPart T ≤ pc_trivialPart T :=
  le_sup_right

/-- The parameter model of parabolic cohomology, `Z / (Z ∩ (coboundaries + Π_i ker(1 − T_i)))`.
Under product one the intersection is the whole second space (`pc_trivialPart_le_Z`).
Source: G32 v0.16, Lemma 6.2 and Proposition 3.1; Brown, Chapter IV, §2. -/
abbrev pc_Vpar {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : Type _ :=
  pc_Z T ⧸ (pc_trivialPart T).comap (pc_Z T).subtype

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : Module K (pc_Vpar T) := inferInstance

/-- The common fixed space `⋂_i ker(T_i − 1)` (for a generating tuple, the invariants `V^G`).
Source: G32 v0.16, Proposition 3.1 (`H⁰(U₀, 𝕍)`); review hlean-rev-hps, H2 correction. -/
def pc_fixed {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : Submodule K (ι → K) :=
  ⨅ i, pc_localFixed T i

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (i : Fin r) : pc_fixed T ≤ pc_localFixed T i :=
  iInf_le _ i

/-- The common fixed space `⋂_i ker(T_iᵀ − 1)` of the transposes (row vectors fixed by every
`T_i`, the invariants of the dual).
Source: G32 v0.16, Proposition 3.1 (`H⁰(U₀, 𝕍^∨)`). -/
def pc_fixedTranspose {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : Submodule K (ι → K) :=
  ⨅ i, LinearMap.ker (Matrix.toLin' ((T i)ᵀ - 1))

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    pc_fixedTranspose (fun _ : Fin 0 => (1 : Matrix ι ι K)) = ⊤ := by
  simp [pc_fixedTranspose]

/-- The cup product of Lemma 6.2 with fibre pairing `h(x, y) = star x ⬝ᵥ (H *ᵥ y)`,
conjugate-linear in the first variable:
`S(a, b) = Σ_i h(Q_i⁻¹ F^a_i + a_i, c^b_i)`.
Source: G32 v0.16, Lemma 6.2 (`lem:cocycle`). -/
def pc_S {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K) (a b : Fin r → ι → K) : K :=
  ∑ i, star ((pc_Q T i)⁻¹ *ᵥ pc_F T a i + a i) ⬝ᵥ (H *ᵥ pc_c T b i)

/-- The rank-24 instance: with the standard form, `pc_S` is the frozen `g32CocycleS`. -/
example (ω : ℂ) (k : Fin 4) (a b : HodgeLean.Papers.G32CocycleParam) :
    pc_S (HodgeLean.Papers.g32CocycleTuple ω k) 1 a b = HodgeLean.Papers.g32CocycleS ω k a b := by
  simp only [pc_S, Matrix.one_mulVec]
  rfl

/-- The rank-24 instance: `pc_Z` is the frozen `G32InCocycleSpace`. -/
example (ω : ℂ) (k : Fin 4) (a : HodgeLean.Papers.G32CocycleParam) :
    a ∈ pc_Z (HodgeLean.Papers.g32CocycleTuple ω k) ↔ HodgeLean.Papers.G32InCocycleSpace ω k a :=
  Iff.rfl

/-- The same pairing written without inverses, `Σ_i h(F^a_i + Q_i a_i, Q_i c^b_i)`; it agrees
with `pc_S` when the form is invariant (`pc_S_eq_invFree`).
Source: G32 v0.16, Lemma 6.2, with `h(Q⁻¹x, y) = h(x, Qy)` for a `Q`-invariant form. -/
def pc_SInvFree {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K) (a b : Fin r → ι → K) : K :=
  ∑ i, star (pc_F T a i + pc_Q T i *ᵥ a i) ⬝ᵥ (H *ᵥ (pc_Q T i *ᵥ pc_c T b i))

example {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K) (a : Fin r → ι → K) :
    pc_SInvFree T H a 0 = 0 := by
  simp [pc_SInvFree, pc_c]

/-- The pairing `pc_S` as a sesquilinear map, conjugate-linear in the first variable.
Source: G32 v0.16, Lemma 6.2 (`lem:cocycle`); `pc_S`. -/
def pc_SForm {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K) :
    (Fin r → ι → K) →ₗ⋆[K] (Fin r → ι → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (pc_S T H)
    (fun a a' b => by
      simp only [pc_S, pc_F, pc_c, Pi.add_apply, Matrix.mulVec_add, Finset.sum_add_distrib,
        star_add, add_dotProduct]
      abel)
    (fun t a b => by
      have hF : ∀ i, pc_F T (t • a) i = t • pc_F T a i := fun i => by
        simp only [pc_F, pc_c, Pi.smul_apply, Matrix.mulVec_smul, Finset.smul_sum]
      simp only [pc_S, hF, Pi.smul_apply, Matrix.mulVec_smul, ← smul_add, star_smul,
        smul_dotProduct, starRingEnd_apply, smul_eq_mul, Finset.mul_sum])
    (fun a b b' => by
      simp only [pc_S, pc_c, Pi.add_apply, Matrix.mulVec_add, dotProduct_add,
        Finset.sum_add_distrib])
    (fun t a b => by
      simp only [pc_S, pc_c, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul,
        RingHom.id_apply, smul_eq_mul, Finset.mul_sum])

example {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K) (a b : Fin r → ι → K) :
    pc_SForm T H a b = pc_S T H a b := rfl

/-- A linear section `V_par → Z` of the quotient map: the inverse of the quotient map restricted
to a chosen complement of `Z ∩ trivial part` in `Z`.
Source: linear algebra over a field (`Submodule.exists_isCompl`,
`Submodule.quotientEquivOfIsCompl`). -/
def pc_lift {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) : pc_Vpar T →ₗ[K] pc_Z T :=
  let p := (pc_trivialPart T).comap (pc_Z T).subtype
  (Classical.choose (Submodule.exists_isCompl p)).subtype ∘ₗ
    (Submodule.quotientEquivOfIsCompl p _
      (Classical.choose_spec (Submodule.exists_isCompl p))).toLinearMap

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (x : pc_Vpar T) : Submodule.Quotient.mk (pc_lift T x) = x :=
  Submodule.mk_quotientEquivOfIsCompl_apply
    (Classical.choose_spec (Submodule.exists_isCompl _)) x

/-- The descended pairing on `V_par`: `pc_S` evaluated on the representatives chosen by
`pc_lift`. Under product one and a Hermitian invariant form it does not depend on the
representatives (`pc_SPar_mk`). For a non-invariant form it is still defined, and it is
sesquilinear by construction.
Source: G32 v0.16, Lemma 6.2 ("vanishes on coboundaries") and proof of Proposition 6.3 (the
form on the quotient by the radical). -/
def pc_SPar {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K) :
    pc_Vpar T →ₗ⋆[K] pc_Vpar T →ₗ[K] K :=
  ((pc_SForm T H).comp ((pc_Z T).subtype ∘ₗ pc_lift T)).compl₂ ((pc_Z T).subtype ∘ₗ pc_lift T)

example {K : Type*} [Field K] [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K) (x y : pc_Vpar T) :
    pc_SPar T H x y = pc_S T H (pc_lift T x) (pc_lift T y) := rfl

/-- The monodromy tuple `T_i = σ(g_i)` of a representation `σ` and a tuple `g` of group
elements (a Nielsen tuple when `g₁ ⋯ g_r = 1` and the `g_i` generate). The coefficients are
`σ` itself, acting on column vectors.
Source: G32 v0.16, §3.1 (Nielsen classes) and Proposition 3.1. -/
def pc_tuple {G : Type*} [Monoid G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G) :
    Fin r → Matrix ι ι K :=
  fun i => σ (g i)

example {G : Type*} [Monoid G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : G →* Matrix ι ι K) :
    pc_tuple σ (fun _ : Fin 2 => (1 : G)) 0 = 1 :=
  σ.map_one

/-- The invariants `V^G = ⋂_{x ∈ G} ker(σ(x) − 1)` of a representation.
Source: G32 v0.16, Proposition 3.1 (`H⁰(U₀, 𝕍)`). -/
def pc_invariants {G : Type*} [Monoid G] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : G →* Matrix ι ι K) : Submodule K (ι → K) :=
  ⨅ x : G, LinearMap.ker (Matrix.toLin' (σ x - 1))

example {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    pc_invariants (1 : Unit →* Matrix ι ι K) = ⊤ := by
  simp [pc_invariants]

/-- The G32 root tuple: the thirteen matrices `b4b_toMatrix (b4b_root j)` on `ℂ⁴`, that is, the
defining reflection representation of `b4b_Group` along the root (B4b's matrix tuple at the
root).
Source: `b4b_root`, `b4b_tuple`; G32 v0.16, Definition 3.5 and Appendix A. -/
def hp_rootTuple : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ :=
  b4b_tuple b4b_root ⟨b4b_root, Relation.EqvGen.refl _⟩

example : hp_rootTuple 0 = HodgeLean.Papers.g32R1 HodgeLean.Papers.g32h_omega := rfl

/-- The six parameter tuples of the H6 certificate, over any field, in terms of an element `ω`
(a primitive cube root of unity in the intended use). The entries were computed by exact
arithmetic over `ℚ(ω)`: a basis of `Z` modulo the trivial part, followed by a change of basis
matching the printed Gram matrix, followed by reduction modulo `Π_i ker(1 − T_i)` to one or
two nonzero coordinates per slot.
Source: exact computation for this spec (`docs/specs/ParabolicCohomology.md`, H6); G32 v0.16,
Lemma 6.2 and Proposition 6.3. -/
def hp_certOver {K : Type*} [Field K] (ω : K) : Fin 6 → Fin 13 → Fin 4 → K :=
  ![![![(2/3 - 2/3 * ω), 0, 0, 0],
      0,
      0,
      0,
      ![(-2/3 + 2/3 * ω), 0, 0, 0],
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      ![0, 0, 0, (-2/3 - 1/3 * ω)]],
    ![![(-1/6 + 2/3 * ω), 0, 0, 0],
      ![(1/6 + 1/3 * ω), 0, 0, 0],
      ![(1/3 + 2/3 * ω), 0, 0, 0],
      0,
      ![(2/3 - 2/3 * ω), 0, 0, 0],
      0,
      ![(-2/3 - 1/3 * ω), 0, 0, 0],
      0,
      0,
      0,
      0,
      0,
      ![0, 0, 0, (1/2 + 1/2 * ω)]],
    ![0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      ![0, (-1/3 + 1/3 * ω), 0, 0],
      0,
      ![0, (-2/3 - 1/3 * ω), 0, 0],
      0,
      0],
    ![![(-1/3 - 2/3 * ω), 0, 0, 0],
      0,
      ![(1/2 + 1/2 * ω), 0, 0, 0],
      ![(1/2 - 1/2 * ω), 0, 0, 0],
      ![(4/3 + 2/3 * ω), 0, 0, 0],
      0,
      ![(-1 - ω), 0, 0, 0],
      0,
      0,
      0,
      0,
      0,
      ![0, 0, 0, (-1/6 + 2/3 * ω)]],
    ![![(-5/6 - 1/2 * ω), 0, 0, 0],
      ![(1/6 + 1/2 * ω), 0, 0, 0],
      ![(7/6 + 7/6 * ω), 0, 0, 0],
      ![(3/2 + 1/2 * ω), 0, 0, 0],
      ![(2 + 4/3 * ω), 0, 0, 0],
      0,
      ![(-2/3 - ω), 0, 0, 0],
      0,
      0,
      0,
      0,
      0,
      ![0, 0, 0, (-1/6 + 5/6 * ω)]],
    ![![1, 0, 0, 0],
      ![1, 0, 0, 0],
      ![(-1 - ω), 0, 0, 0],
      ![(-1 - ω), 0, 0, 0],
      0,
      0,
      0,
      0,
      ![0, (-1/3 - 2/3 * ω), 0, 0],
      ![0, 0, 0, (-2/3 - 2/3 * ω)],
      ![0, (-1/3 + 1/3 * ω), 0, 0],
      0,
      ![0, 0, 0, (-1/3 - 2/3 * ω)]]]

example {K : Type*} [Field K] (ω : K) : hp_certOver ω 5 0 0 = 1 := rfl

/-- The six certificate tuples at `ω = g32h_omega`, as parameters for `hp_rootTuple`.
Source: `hp_certOver`; G32 v0.16, Lemma 6.2. -/
def hp_cert : Fin 6 → Fin 13 → Fin 4 → ℂ := hp_certOver HodgeLean.Papers.g32h_omega

example : hp_cert 2 8 1 = -1/3 + 1/3 * HodgeLean.Papers.g32h_omega := rfl

/-! ## The root and the certificate over `K = ℚ(√−3)` -/

/-- The field `K = ℚ(√−3)` of `g32d_ParabolicPolarization`, with `omega² = −3`.
Source: `g32d_ParabolicPolarization` (`G32DiscDefs.lean`); G32 v0.16, §1 (`K = ℚ(√−3)`). -/
abbrev hp_K : Type := QuadraticAlgebra ℚ (-3) 0

example : (QuadraticAlgebra.omega : hp_K) * QuadraticAlgebra.omega = -3 := by
  ext <;> simp <;> rfl

/-- The primitive cube root of unity `ζ = (−1 + √−3)/2` of `K`, as in
`g32d_ParabolicPolarization`.
Source: `g32d_ParabolicPolarization` (`ζ := (-1 + QuadraticAlgebra.omega) / 2`). -/
def pc_zeta : hp_K := (-1 + QuadraticAlgebra.omega) / 2

example : pc_zeta = (-1 + QuadraticAlgebra.omega) / 2 := rfl

/-- The complex embedding of `K` sending `√−3` to `i·√3` (so `ζ` goes to `e^{2πi/3}`).
Source: `QuadraticAlgebra.lift`; `g32h_omega = exp(2πi/3)`. -/
def hp_embed : hp_K →+* ℂ :=
  (QuadraticAlgebra.lift ⟨Complex.I * (Real.sqrt 3 : ℂ), by
    rw [mul_mul_mul_comm, Complex.I_mul_I, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    simp⟩ : hp_K →ₐ[ℚ] ℂ).toRingHom

example : hp_embed QuadraticAlgebra.omega = Complex.I * (Real.sqrt 3 : ℂ) := by
  simp [hp_embed]

/-- The four printed generators `r₁, r₂, x, y` over any field, in terms of `ω`.
Source: G32 v0.16, Appendix A; `b4b_generators`. -/
def hp_genOver {K : Type*} [Field K] (ω : K) : Fin 4 → Matrix (Fin 4) (Fin 4) K :=
  ![HodgeLean.Papers.g32R1 ω, HodgeLean.Papers.g32R2 ω, HodgeLean.Papers.g32X ω,
    HodgeLean.Papers.g32Y ω]

example {K : Type*} [Field K] (ω : K) : hp_genOver ω 2 = HodgeLean.Papers.g32X ω := rfl

/-- The conjugate `h r₁ h⁻¹` of the first reflection by the product `h` of a word in the printed
generators, over any field (matrix inverse).
Source: G32 v0.16, Appendix A and Definition 3.5; `b4b_reflection`. -/
def hp_reflOver {K : Type*} [Field K] (ω : K) (w : List (Fin 4)) : Matrix (Fin 4) (Fin 4) K :=
  let h := (w.map (hp_genOver ω)).prod
  h * HodgeLean.Papers.g32R1 ω * h⁻¹

example {K : Type*} [Field K] (ω : K) : hp_reflOver ω [] = HodgeLean.Papers.g32R1 ω := by
  simp [hp_reflOver]

/-- The thirteen entries of `b4b_root` written over any field, with group inverses replaced by
matrix inverses: the same words in the printed generators, in the same order.
Source: `b4b_root`; G32 v0.16, Definition 3.5 and Appendix A. -/
def hp_rootTupleOver {K : Type*} [Field K] (ω : K) : Fin 13 → Matrix (Fin 4) (Fin 4) K :=
  ![HodgeLean.Papers.g32R1 ω, (HodgeLean.Papers.g32R1 ω)⁻¹,
    (HodgeLean.Papers.g32R2 ω)⁻¹, HodgeLean.Papers.g32R2 ω,
    hp_reflOver ω [2], (hp_reflOver ω [2])⁻¹,
    hp_reflOver ω [3], (hp_reflOver ω [3])⁻¹,
    hp_reflOver ω [1, 3, 1], (hp_reflOver ω [0, 0, 2])⁻¹,
    hp_reflOver ω [3, 2], (hp_reflOver ω [3, 2, 1])⁻¹,
    HodgeLean.Papers.g32X ω ^ 2]

example {K : Type*} [Field K] (ω : K) : hp_rootTupleOver ω 12 = HodgeLean.Papers.g32X ω ^ 2 := rfl

/-- The G32 root tuple over `K = ℚ(√−3)`, at `ζ = (−1 + √−3)/2`.
Source: `hp_rootTupleOver`; `g32d_ParabolicPolarization`. -/
def hp_rootTupleK : Fin 13 → Matrix (Fin 4) (Fin 4) hp_K := hp_rootTupleOver pc_zeta

example : hp_rootTupleK 0 = HodgeLean.Papers.g32R1 pc_zeta := rfl

/-- The six certificate tuples over `K`, at `ζ`, as parameters for `hp_rootTupleK`.
Source: `hp_certOver`; G32 v0.16, Lemma 6.2. -/
def hp_certK : Fin 6 → Fin 13 → Fin 4 → hp_K := hp_certOver pc_zeta

example : hp_certK 5 0 0 = 1 := rfl

end HodgeLean.Foundations.Program

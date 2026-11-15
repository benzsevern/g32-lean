import HodgeLean.Foundations.Program.SchlesingerPathDefs
import HodgeLean.Foundations.Program.KernelFramesDefs

/-! # B6-5 stage 5d, family part: Laurent systems, frames and numerators along the path

The parameter-dependent Laurent-coefficient systems of G32 v0.16, §5.5(2)–(7), written as
explicit functions of the poles, the residues, the fixed-pole eigenbases and the moving-pole left
eigenvectors at one parameter; the normalized eigenbases and left eigenvectors as explicit
functions of the residues; the inverse-block frames, the rational vectors they define, the
branch polynomial `D_θ`, the products `D_θ q_bᵀ r_a` and the ordered `9 × 10` numerator array;
and the order-condition spaces of the differential dictionary, on the `s`-line, for a supplied
normal-form gauge at each fixed pole. Every family object is evaluated on the residues of a 5c
record through `b65q_res`. No statement is asserted here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The literal eigenbasis at `1` and `−2`: transposed reduced-echelon bases of the two
eigenspaces of `3B_∞`, eigenvalue `−2` first.
Source: G32 v0.16, §5.5(2); `docs/specs/KernelFrames.md`, the displayed eigenbasis. -/
def b65q_E : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 1, 0;
     0, 1, 0, 1;
     -34391/11197440, 14161/5598720, 14161/11197440, 14161/5598720;
     119/11, -252/11, 7/187, 36/187]

example : b65q_E 3 1 = -252/11 := by simp [b65q_E]

/-- The initial ordered eigenbases at the fixed poles `0, 3, 1, −2`: the identity at `0` and
`3`, and `b65q_E` at `1` and `−2`.
Source: G32 v0.16, §5.5(2), reduced echelon bases ordered by increasing eigenvalue. -/
def b65q_eigen0 : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := ![1, 1, b65q_E, b65q_E]

example : b65q_eigen0 2 = b65q_E := rfl

/-- **Non-degeneracy.** `b65q_E` is an eigenbasis of the residue `3B_∞` at `1`, with the
exponents `(−2, −2, 2, 2)` in this order. -/
example : b65p_fixedResidue 2 * b65q_E = b65q_E * diagonal (b65p_exponents 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b65p_fixedResidue, b65q_E, b65p_exponents, b65r_Binf, b65r_B0, b65r_B5,
      b65r_Bneg7, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal] <;> norm_num

/-- The matrix of a residue operator on `ℂ⁴`.
Source: Mathlib `LinearMap.toMatrix'`; G32 v0.16, Appendix A, column-vector convention. -/
def b65q_mat (L : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) : Matrix (Fin 4) (Fin 4) ℂ :=
  LinearMap.toMatrix' (L : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ))

example (M : Matrix (Fin 4) (Fin 4) ℂ) : b65q_mat (b65r_operator M) = M := by
  ext i j
  simp [b65q_mat, b65r_operator, LinearMap.toMatrix'_apply, Matrix.mulVec, dotProduct,
    Pi.single_apply]

/-- The residue matrices of a residue path at parameter `θ`.
Source: `b65p_Outputs.residue`; `b65q_mat`. -/
def b65q_res (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ)
    (q : Fin 4 ⊕ Fin 12) : Matrix (Fin 4) (Fin 4) ℂ :=
  b65q_mat (R θ q)

example (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) q :
    b65q_res R θ q = b65q_mat (R θ q) := rfl

/-- The Taylor coefficient of order `l` at the fixed pole `k` of the regular part
`Σ_{q ≠ k} A_q/(s − t_q)`: `−Σ_{q ≠ k} A_q/(t_q − t_k)^{l+1}`.
Source: G32 v0.16, §5.3, the Taylor coefficients of Σ_{q≠p} A_q/(s − q) in the recursion. -/
def b65q_taylor (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (k : Fin 4) (l : ℕ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ q, if q = Sum.inl k then 0 else (-((t q - t (Sum.inl k)) ^ (l + 1))⁻¹) • A q

example (t : Fin 4 ⊕ Fin 12 → ℂ) (k : Fin 4) (l : ℕ) : b65q_taylor t 0 k l = 0 := by
  simp [b65q_taylor]

/-- The regular part `Σ_{q ≠ k} (s − t_q)⁻¹ A_q` at the fixed pole `k`, as a matrix.
Source: G32 v0.16, §5.3; `b65p_regularPart`. -/
def b65q_regular (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (k : Fin 4) (s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ q, if q = Sum.inl k then 0 else (s - t q)⁻¹ • A q

example (t : Fin 4 ⊕ Fin 12 → ℂ) (k : Fin 4) (s : ℂ) : b65q_regular t 0 k s = 0 := by
  simp [b65q_regular]

/-- The first `N + 1` Taylor coefficients `H_0, …, H_N` of the normal-form gauge at the fixed
pole `k`, for the eigenbasis `P`: `H_0 = 1` and
`(n + λ_j − λ_i) (H_n)_{ij} = (Σ_{l<n} (P⁻¹ G_l P) H_{n−1−l})_{ij}`, with every free resonant
entry (zero denominator) equal to `0`. Entries beyond `N` are `0`.
Source: G32 v0.16, §5.3 (the recursion) and §5.5(2) (free resonant entries equal to 0). -/
def b65q_gaugeUpTo (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) : ℕ → ℕ → Matrix (Fin 4) (Fin 4) ℂ
  | 0 => fun m ↦ if m = 0 then 1 else 0
  | N + 1 => Function.update (b65q_gaugeUpTo t A P k N) (N + 1)
      (Matrix.of fun i j ↦
        if ((N + 1 : ℕ) : ℂ) + b65p_exponents k j - b65p_exponents k i = 0 then 0 else
          (∑ l ∈ Finset.range (N + 1),
              (P⁻¹ * b65q_taylor t A k l * P) * b65q_gaugeUpTo t A P k N (N - l)) i j /
            (((N + 1 : ℕ) : ℂ) + b65p_exponents k j - b65p_exponents k i))

example (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) :
    b65q_gaugeUpTo t A P k 1 0 = 1 := by
  simp [b65q_gaugeUpTo]

/-- The Taylor coefficient `H_n` of the normal-form gauge with zero free resonant entries.
Source: G32 v0.16, §5.3 and §5.5(2). -/
def b65q_gauge (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (n : ℕ) : Matrix (Fin 4) (Fin 4) ℂ :=
  b65q_gaugeUpTo t A P k n n

example (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) : b65q_gauge t A P k 0 = 1 := by
  simp [b65q_gauge, b65q_gaugeUpTo]

/-- The first `N + 1` coefficients of the inverse of a power series with constant term `1`:
`H⁻¹_0 = 1`, `H⁻¹_n = −Σ_{m=1}^{n} H_m H⁻¹_{n−m}`.
Source: inversion of formal power series with invertible constant term. -/
def b65q_seriesInvUpTo (H : ℕ → Matrix (Fin 4) (Fin 4) ℂ) : ℕ → ℕ → Matrix (Fin 4) (Fin 4) ℂ
  | 0 => fun m ↦ if m = 0 then 1 else 0
  | N + 1 => Function.update (b65q_seriesInvUpTo H N) (N + 1)
      (-∑ m ∈ Finset.range (N + 1), H (m + 1) * b65q_seriesInvUpTo H N (N - m))

example (H : ℕ → Matrix (Fin 4) (Fin 4) ℂ) :
    b65q_seriesInvUpTo H 1 1 = -H 1 := by
  simp [b65q_seriesInvUpTo]

/-- The coefficient of order `n` of the inverse power series.
Source: inversion of formal power series with invertible constant term. -/
def b65q_seriesInv (H : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (n : ℕ) : Matrix (Fin 4) (Fin 4) ℂ :=
  b65q_seriesInvUpTo H n n

example (H : ℕ → Matrix (Fin 4) (Fin 4) ℂ) : b65q_seriesInv H 0 = 1 := by
  simp [b65q_seriesInv, b65q_seriesInvUpTo]

/-- The Taylor coefficients at the fixed pole `k` of `(P_k H_k)⁻¹ = H_k⁻¹ P_k⁻¹`, read by the
r-conditions.
Source: G32 v0.16, Lemma 5.3 (dictionary): the components of (P_p H_p)⁻¹ r. -/
def b65q_rCoeff (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (n : ℕ) : Matrix (Fin 4) (Fin 4) ℂ :=
  b65q_seriesInv (b65q_gauge t A (P k) k) n * (P k)⁻¹

example (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) :
    b65q_rCoeff t A 1 k 0 = 1 := by
  simp [b65q_rCoeff, b65q_seriesInv, b65q_seriesInvUpTo]

/-- The Taylor coefficients at the fixed pole `k` of `(P_k H_k)ᵀ`, read by the q-conditions.
Source: G32 v0.16, Lemma 5.3 (dictionary): the components of (P_p H_p)ᵀ q. -/
def b65q_qCoeff (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (n : ℕ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (P k * b65q_gauge t A (P k) k n)ᵀ

example (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) :
    b65q_qCoeff t A 1 k 0 = 1 := by
  simp [b65q_qCoeff, b65q_gauge, b65q_gaugeUpTo]

/-- The 41 finite r-rows `(pole, component, order)`: ordered by pole `0, 3, 1, −2`, then
component, then order from `−3` to `⌊λ_{p,j}⌋ − 1`.
Source: G32 v0.16, §5.5(5). -/
def b65q_rRow : Fin 41 → Fin 4 × Fin 4 × ℤ :=
  ![(0, 0, -3), (0, 1, -3), (0, 1, -2), (0, 2, -3), (0, 2, -2), (0, 3, -3), (0, 3, -2),
    (0, 3, -1), (0, 3, 0), (1, 1, -3), (1, 2, -3), (1, 3, -3), (1, 3, -2), (1, 3, -1),
    (1, 3, 0), (1, 3, 1), (1, 3, 2), (2, 0, -3), (2, 1, -3), (2, 2, -3), (2, 2, -2),
    (2, 2, -1), (2, 2, 0), (2, 2, 1), (2, 3, -3), (2, 3, -2), (2, 3, -1), (2, 3, 0),
    (2, 3, 1), (3, 0, -3), (3, 1, -3), (3, 2, -3), (3, 2, -2), (3, 2, -1), (3, 2, 0),
    (3, 2, 1), (3, 3, -3), (3, 3, -2), (3, 3, -1), (3, 3, 0), (3, 3, 1)]

/-- Each listed r-order lies below `⌊λ_{p,j}⌋`. -/
example : ∀ x : Fin 41, (b65q_rRow x).2.2 + 1 ≤
    (![![-2, -1, -1, 1], ![-3, -2, -2, 3], ![-2, -2, 2, 2], ![-2, -2, 2, 2]] : Fin 4 → Fin 4 → ℤ)
      (b65q_rRow x).1 (b65q_rRow x).2.1 := by decide

/-- The 53 finite q-rows `(pole, component, order)`, with orders from `−3` to
`⌊−λ_{p,j}⌋ − 1`.
Source: G32 v0.16, §5.5(5). -/
def b65q_qRow : Fin 53 → Fin 4 × Fin 4 × ℤ :=
  ![(0, 0, -3), (0, 0, -2), (0, 0, -1), (0, 0, 0), (0, 1, -3), (0, 1, -2), (0, 1, -1),
    (0, 1, 0), (0, 2, -3), (0, 2, -2), (0, 2, -1), (0, 2, 0), (0, 3, -3), (1, 0, -3),
    (1, 0, -2), (1, 0, -1), (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 1, -3), (1, 1, -2),
    (1, 1, -1), (1, 1, 0), (1, 1, 1), (1, 2, -3), (1, 2, -2), (1, 2, -1), (1, 2, 0),
    (1, 2, 1), (2, 0, -3), (2, 0, -2), (2, 0, -1), (2, 0, 0), (2, 0, 1), (2, 1, -3),
    (2, 1, -2), (2, 1, -1), (2, 1, 0), (2, 1, 1), (2, 2, -3), (2, 3, -3), (3, 0, -3),
    (3, 0, -2), (3, 0, -1), (3, 0, 0), (3, 0, 1), (3, 1, -3), (3, 1, -2), (3, 1, -1),
    (3, 1, 0), (3, 1, 1), (3, 2, -3), (3, 3, -3)]

/-- Each listed q-order lies below `⌊−λ_{p,j}⌋`. -/
example : ∀ x : Fin 53, (b65q_qRow x).2.2 + 1 ≤
    (![![1, 1, 1, -2], ![3, 2, 2, -3], ![2, 2, -2, -2], ![2, 2, -2, -2]] : Fin 4 → Fin 4 → ℤ)
      (b65q_qRow x).1 (b65q_qRow x).2.1 := by decide

/-- The coefficient of `(s − t_k)ⁿ` in component `j` of `K(s) · e_i (s − t_b)^{−m}`, where the
unknown column `c = 4a + i` is the coordinate `i` of the coefficient of `(s − t_b)^{−m}`,
`b = b65k_poleIndex a`, `m = b65k_poleOrder a`, and `K k n` are the Taylor coefficients of `K`
at `t_k`. At `b ≠ k` it uses `(s − t_b)^{−m} = Σ_l (−1)^l C(m+l−1, l) (t_k − t_b)^{−m−l}
(s − t_k)^l`.
Source: G32 v0.16, Lemma 5.4 (kernel)(1),(2) and §5.5(4)–(5). -/
def b65q_principalEntry (t : Fin 4 ⊕ Fin 12 → ℂ) (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (k j : Fin 4) (n : ℤ) (c : Fin 36) : ℂ :=
  if b65k_poleIndex ⟨c.val / 4, by omega⟩ = k then
    (if 0 ≤ n + b65k_poleOrder ⟨c.val / 4, by omega⟩ then
      K k (n + b65k_poleOrder ⟨c.val / 4, by omega⟩).toNat j ⟨c.val % 4, by omega⟩ else 0)
  else if 0 ≤ n then
    ∑ l ∈ Finset.range (n.toNat + 1), K k (n.toNat - l) j ⟨c.val % 4, by omega⟩ *
      ((-1) ^ l * ((b65k_poleOrder ⟨c.val / 4, by omega⟩ + l - 1).choose l : ℂ) *
        ((t (Sum.inl k) - t (Sum.inl (b65k_poleIndex ⟨c.val / 4, by omega⟩))) ^
          (b65k_poleOrder ⟨c.val / 4, by omega⟩ + l))⁻¹)
  else 0

example (t : Fin 4 ⊕ Fin 12 → ℂ) (k j : Fin 4) (c : Fin 36) :
    b65q_principalEntry t 0 k j (-1) c = 0 := by
  unfold b65q_principalEntry
  split_ifs <;> simp

/-- The coefficient of `s^{−1}` at `∞` in the coordinate `i` of the principal part with unknown
column `c`: `1` exactly for the simple-pole coefficient of coordinate `i`.
Source: G32 v0.16, Lemma 5.4 (kernel)(2), the coefficient of s^{−1} at ∞. -/
def b65q_infinityEntry (i : Fin 4) (c : Fin 36) : ℂ :=
  if b65k_poleOrder ⟨c.val / 4, by omega⟩ = 1 ∧ c.val % 4 = i.val then 1 else 0

example : b65q_infinityEntry 0 0 = 1 := by simp [b65q_infinityEntry, b65k_poleOrder]

/-- **The r-system** at one parameter: 45 rows (41 Laurent conditions at the fixed poles, then
the four coordinates at `∞`) and 36 unknown columns, for poles `t`, residues `A` and ordered
eigenbases `P` at the fixed poles.
Source: G32 v0.16, Lemma 5.3 (dictionary), Lemma 5.4 (kernel), §5.5(2),(4),(5). -/
def b65q_rSystem (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 45) (Fin 36) ℂ := fun r c ↦
  if h : r.val < 41 then
    b65q_principalEntry t (b65q_rCoeff t A P) (b65q_rRow ⟨r.val, h⟩).1
      (b65q_rRow ⟨r.val, h⟩).2.1 (b65q_rRow ⟨r.val, h⟩).2.2 c
  else b65q_infinityEntry ⟨r.val - 41, by omega⟩ c

/-- **Non-degeneracy.** Every r-system has the infinity entry `1` at row `41`, column `0`, so
none is the zero matrix. -/
example (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : b65q_rSystem t A P 41 0 = 1 := by
  simp [b65q_rSystem, b65q_infinityEntry]
  decide

/-- The two fibres `5, −7` of the reflection poles.
Source: G32 v0.16, §5.2, P₅ and P₋₇. -/
def b65q_fibreValue : Fin 2 → ℤ := ![5, -7]

example : b65q_fibreValue 1 = -7 := rfl

/-- The fibre index (`0` over `5`, `1` over `−7`) of a labelled reflection pole.
Source: `b65p_fibre`. -/
def b65q_fibreIndex (j : Fin 12) : Fin 2 := if b65p_fibre j = 5 then 0 else 1

example : ∀ j, b65q_fibreValue (b65q_fibreIndex j) = b65p_fibre j := by decide

/-- The coefficient of `(s − t_k)ⁿ` in component `j` of `K(s)` applied to the beta column
`(e, v)`: `Σ_{t over e} node_t^v · w_t/(s − t)`, the residue at the moving pole `t` being
`β_e(node_t) w_t` with `β_e(x) = Σ_v β_{e,v} x^v`.
Source: G32 v0.16, §5.5(4) (Lagrange interpolation of the residue multiples). -/
def b65q_betaEntry (t : Fin 4 ⊕ Fin 12 → ℂ) (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ) (k j : Fin 4) (n : ℤ) (e : Fin 2)
    (v : Fin 6) : ℂ :=
  if 0 ≤ n then
    ∑ x : Fin 12, if b65q_fibreIndex x = e then node x ^ v.val *
      ∑ l ∈ Finset.range (n.toNat + 1),
        (K k (n.toNat - l) *ᵥ w x) j * (-((t (Sum.inr x) - t (Sum.inl k)) ^ (l + 1))⁻¹)
      else 0
  else 0

example (t : Fin 4 ⊕ Fin 12 → ℂ) (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (node : Fin 12 → ℂ) (k j : Fin 4) (n : ℤ) (e : Fin 2) (v : Fin 6) :
    b65q_betaEntry t K node 0 k j n e v = 0 := by
  simp [b65q_betaEntry]

/-- The coefficient of `s^{−1}` at `∞` in coordinate `i` for the beta column `(e, v)`.
Source: G32 v0.16, §5.5(5), the coefficient of s^{−1} at ∞. -/
def b65q_betaInfinity (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ) (i : Fin 4) (e : Fin 2)
    (v : Fin 6) : ℂ :=
  ∑ x : Fin 12, if b65q_fibreIndex x = e then node x ^ v.val * w x i else 0

example (node : Fin 12 → ℂ) (i : Fin 4) (e : Fin 2) (v : Fin 6) :
    b65q_betaInfinity node 0 i e v = 0 := by
  simp [b65q_betaInfinity]

/-- **The q-system** at one parameter: 57 rows (53 Laurent conditions at the fixed poles, then
the four coordinates at `∞`) and 48 columns (36 fixed-pole unknowns, then `β_{5,0..5}`,
`β_{−7,0..5}`), for poles `t`, residues `A`, eigenbases `P`, interpolation nodes `node` and
moving-pole left eigenvectors `w`.
Source: G32 v0.16, Lemma 5.3 (dictionary), Lemma 5.4 (kernel), §5.5(2)–(5). -/
def b65q_qSystem (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ) :
    Matrix (Fin 57) (Fin 48) ℂ := fun r c ↦
  if h : r.val < 53 then
    if hc : c.val < 36 then
      b65q_principalEntry t (b65q_qCoeff t A P) (b65q_qRow ⟨r.val, h⟩).1
        (b65q_qRow ⟨r.val, h⟩).2.1 (b65q_qRow ⟨r.val, h⟩).2.2 ⟨c.val, hc⟩
    else
      b65q_betaEntry t (b65q_qCoeff t A P) node w (b65q_qRow ⟨r.val, h⟩).1
        (b65q_qRow ⟨r.val, h⟩).2.1 (b65q_qRow ⟨r.val, h⟩).2.2 ⟨(c.val - 36) / 6, by omega⟩
        ⟨(c.val - 36) % 6, by omega⟩
  else
    if hc : c.val < 36 then b65q_infinityEntry ⟨r.val - 53, by omega⟩ ⟨c.val, hc⟩
    else b65q_betaInfinity node w ⟨r.val - 53, by omega⟩ ⟨(c.val - 36) / 6, by omega⟩
      ⟨(c.val - 36) % 6, by omega⟩

/-- **Non-degeneracy.** Every q-system has the infinity entry `1` at row `53`, column `0`. -/
example (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ) :
    b65q_qSystem t A P node w 53 0 = 1 := by
  simp [b65q_qSystem, b65q_infinityEntry]
  decide

/-- The spectral projector of `A` for the eigenvalue `μ`, as the Lagrange polynomial in `A` over
the distinct values of the exponent list `λ`.
Source: G32 v0.16, proof of Lemma 5.8 (spectral projectors of A_p(θ) for its constant
eigenvalues); Lagrange interpolation. -/
def b65q_projector (A : Matrix (Fin 4) (Fin 4) ℂ) (lam : Fin 4 → ℂ) (μ : ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Polynomial.aeval A (∏ ν ∈ (Finset.univ.image lam).erase μ,
    (Polynomial.C (μ - ν)⁻¹ * (Polynomial.X - Polynomial.C ν)))

example (A : Matrix (Fin 4) (Fin 4) ℂ) (μ : ℂ) :
    b65q_projector A (fun _ ↦ μ) μ = 1 := by
  simp [b65q_projector, Finset.image_const Finset.univ_nonempty]

/-- The normalized eigenbasis `P(θ) = P₀(1 + Y(θ))`, `Y` zero between equal eigenvalues: its
column `i` is the unique vector of the `λ_i`-eigenspace of `A` whose `P₀`-coordinates in the
`λ_i`-block are `e_i`, namely `Π(A) (Π(A₀) Π(A) + 1 − Π(A₀))⁻¹ P₀ e_i` with `Π` the
`λ_i`-projector and `A₀` the initial residue.
Source: G32 v0.16, §5.5(2), the normalization of P_p(θ). -/
def b65q_eigenbasis (A A₀ P₀ : Matrix (Fin 4) (Fin 4) ℂ) (lam : Fin 4 → ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun r i ↦
  (b65q_projector A lam (lam i) *
    (b65q_projector A₀ lam (lam i) * b65q_projector A lam (lam i) + 1 -
      b65q_projector A₀ lam (lam i))⁻¹ * P₀) r i

example (A₀ P₀ : Matrix (Fin 4) (Fin 4) ℂ) (μ : ℂ) :
    b65q_eigenbasis A₀ A₀ P₀ (fun _ ↦ μ) = P₀ := by
  ext r i
  simp [b65q_eigenbasis, b65q_projector, Finset.image_const Finset.univ_nonempty]

/-- The vectors `u₁`, `u₂` of the rank-one residues `B₅ = u₁v₁ᵀ`, `B₋₇ = u₂v₂ᵀ`.
Source: G32 v0.16, Appendix A; `b65r_B5`, `b65r_Bneg7`. -/
def b65q_u : Fin 2 → Fin 4 → ℂ :=
  ![![1, 1, 0, 1], ![-5598720/14161, 0, 1, 5598720/22253]]

example : b65q_u 0 3 = 1 := rfl

/-- The left eigenvector of a rank-one residue `A` for its nonzero eigenvalue `tr A`,
normalized by `wᵀu = tr A`: `w = (tr A / (uᵀAu)) · Aᵀu`.
Source: G32 v0.16, §5.5(3), w_t(θ) with w_t(θ)ᵀu_i = 1/3 or 2/3. -/
def b65q_leftEigen (A : Matrix (Fin 4) (Fin 4) ℂ) (u : Fin 4 → ℂ) : Fin 4 → ℂ :=
  (Matrix.trace A / (u ᵥ* A ⬝ᵥ u)) • (u ᵥ* A)

/-- **Non-degeneracy.** At `B₅` the normalized left eigenvector is the printed `v₁`. -/
example : b65q_leftEigen b65r_B5 (b65q_u 0) = ![119/648, 28/135, -41472/289, -187/3240] := by
  ext i
  fin_cases i <;>
    simp [b65q_leftEigen, b65r_B5, b65q_u, Matrix.trace, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ] <;> norm_num

/-- The normalized eigenbases at the fixed poles along a residue path.
Source: G32 v0.16, §5.5(2); `b65q_eigenbasis`, `b65q_eigen0`. -/
def b65q_basis (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) (k : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  b65q_eigenbasis (b65q_res R θ (Sum.inl k)) (b65q_res R 0 (Sum.inl k)) (b65q_eigen0 k)
    (b65p_exponents k)

example (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) (k : Fin 4) :
    b65q_basis R θ k = b65q_eigenbasis (b65q_res R θ (Sum.inl k)) (b65q_res R 0 (Sum.inl k))
      (b65q_eigen0 k) (b65p_exponents k) := rfl

/-- The normalized moving-pole left eigenvectors along a residue path.
Source: G32 v0.16, §5.5(3); `b65q_leftEigen`. -/
def b65q_left (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) (j : Fin 12) :
    Fin 4 → ℂ :=
  b65q_leftEigen (b65q_res R θ (Sum.inr j)) (b65q_u (b65q_fibreIndex j))

example (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) (j : Fin 12) :
    b65q_left R θ j = b65q_leftEigen (b65q_res R θ (Sum.inr j)) (b65q_u (b65q_fibreIndex j)) :=
  rfl

/-- The r-system along the path, for the labelled reflection poles `p` and the residue path `R`.
Source: G32 v0.16, §5.5(2)–(5); `b65q_rSystem`, `b65p_poles`. -/
def b65q_rFamily (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (θ : ℂ) : Matrix (Fin 45) (Fin 36) ℂ :=
  b65q_rSystem (b65p_poles p θ) (b65q_res R θ) (b65q_basis R θ)

example (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) :
    b65q_rFamily p R θ 41 0 = 1 := by
  simp [b65q_rFamily, b65q_rSystem, b65q_infinityEntry]
  decide

/-- The q-system along the path; the interpolation nodes are the labelled roots `p` at `θ = 0`.
Source: G32 v0.16, §5.5(2)–(5); `b65q_qSystem`. -/
def b65q_qFamily (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (θ : ℂ) : Matrix (Fin 57) (Fin 48) ℂ :=
  b65q_qSystem (b65p_poles p θ) (b65q_res R θ) (b65q_basis R θ) p (b65q_left R θ)

example (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) :
    b65q_qFamily p R θ 53 0 = 1 := by
  simp [b65q_qFamily, b65q_qSystem, b65q_infinityEntry]
  decide

/-- The inverse-block r-frame along the path: identity on the free columns `[10, 22, 30]` and
`−block⁻¹ · freeColumns` on the pivot columns, with the rows and columns of `b65k_`.
Source: G32 v0.16, Lemma 5.4 (kernel)(3), §5.5(6). -/
def b65q_rFrame (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (θ : ℂ) : Matrix (Fin 36) (Fin 3) ℂ := fun i f ↦
  (∑ a : Fin 3, if i = b65k_rFree a then (if a = f then 1 else 0) else 0) -
    ∑ a : Fin 33, if i = b65k_rPivot a then
      (((b65q_rFamily p R θ).submatrix b65k_rRows b65k_rPivot)⁻¹ *
        (b65q_rFamily p R θ).submatrix b65k_rRows b65k_rFree) a f else 0

/-- **Non-degeneracy.** Each r-frame column has its own free coordinate `1`, at every
parameter. -/
example (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ)
    (f : Fin 3) : b65q_rFrame p R θ (b65k_rFree f) f = 1 := by
  fin_cases f
  all_goals norm_num [b65q_rFrame, b65k_rFree, b65k_rPivot, Fin.sum_univ_succ]
  all_goals decide

/-- The inverse-block q-frame along the path: identity on the free columns `[42, 46, 47]`.
Source: G32 v0.16, Lemma 5.4 (kernel)(3), §5.5(6). -/
def b65q_qFrame (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (θ : ℂ) : Matrix (Fin 48) (Fin 3) ℂ := fun i f ↦
  (∑ a : Fin 3, if i = b65k_qFree a then (if a = f then 1 else 0) else 0) -
    ∑ a : Fin 45, if i = b65k_qPivot a then
      (((b65q_qFamily p R θ).submatrix b65k_qRows b65k_qPivot)⁻¹ *
        (b65q_qFamily p R θ).submatrix b65k_qRows b65k_qFree) a f else 0

/-- **Non-degeneracy.** Each q-frame column has its own free coordinate `1`. -/
example (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ)
    (f : Fin 3) : b65q_qFrame p R θ (b65k_qFree f) f = 1 := by
  fin_cases f
  all_goals norm_num [b65q_qFrame, b65k_qFree, b65k_qPivot, Fin.sum_univ_succ]
  all_goals decide

/-- The rational vector `r = Σ_{p,k} c_{p,k} (s − p)^{−k}` of fixed-pole principal parts with
coefficient vector `c`, in the column order of `b65k_principal`.
Source: G32 v0.16, Lemma 5.4 (kernel)(1), §5.5(4). -/
def b65q_principal (t : Fin 4 ⊕ Fin 12 → ℂ) (c : Fin 36 → ℂ) (j : Fin 4) : RatFunc ℂ :=
  ∑ a : Fin 9, RatFunc.C (c ⟨4 * a.val + j.val, by omega⟩) /
    (RatFunc.X - RatFunc.C (t (Sum.inl (b65k_poleIndex a)))) ^ b65k_poleOrder a

example (t : Fin 4 ⊕ Fin 12 → ℂ) (j : Fin 4) : b65q_principal t 0 j = 0 := by
  simp [b65q_principal]

/-- The rational vector of a q-coefficient vector `d`: the fixed-pole principal parts plus
`Σ_t β_e(node_t) w_t/(s − t)` over the moving poles.
Source: G32 v0.16, Lemma 5.4 (kernel)(1), §5.5(3)–(4). -/
def b65q_qVector (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (j : Fin 4) : RatFunc ℂ :=
  b65q_principal t (fun i ↦ d ⟨i.val, by omega⟩) j +
    ∑ x : Fin 12, RatFunc.C ((∑ v : Fin 6,
        d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x j) /
      (RatFunc.X - RatFunc.C (t (Sum.inr x)))

example (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ) (j : Fin 4) :
    b65q_qVector t node w 0 j = 0 := by
  simp [b65q_qVector, b65q_principal]

/-- The monic branch polynomial `D(s) = s · Π_t (s − t)` over the twelve moving poles.
Source: G32 v0.16, §5.5(7), D_θ = s D_{5,θ} D_{−7,θ}. -/
def b65q_denominator (t : Fin 4 ⊕ Fin 12 → ℂ) : ℂ[X] :=
  X * ∏ x : Fin 12, (X - C (t (Sum.inr x)))

/-- **Non-degeneracy.** The branch polynomial is monic of degree thirteen for every pole
configuration. -/
example (t : Fin 4 ⊕ Fin 12 → ℂ) :
    (b65q_denominator t).Monic ∧ (b65q_denominator t).natDegree = 13 := by
  have hm : (∏ x : Fin 12, (X - C (t (Sum.inr x)))).Monic :=
    monic_prod_of_monic _ _ fun x _ ↦ monic_X_sub_C _
  refine ⟨monic_X.mul hm, ?_⟩
  rw [b65q_denominator, (monic_X).natDegree_mul hm, natDegree_X,
    natDegree_prod_of_monic _ _ fun x _ ↦ monic_X_sub_C _]
  simp

/-- The product `D(s) · q(d)ᵀ r(c)` of an r-coefficient vector `c` and a q-coefficient
vector `d`.
Source: G32 v0.16, Lemma 5.3 (dictionary), μ(r ⊗ q) = qᵀr ds², and §5.5(7). -/
def b65q_product (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (c : Fin 36 → ℂ) (d : Fin 48 → ℂ) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator t) *
    ∑ j : Fin 4, b65q_qVector t node w d j * b65q_principal t c j

example (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) : b65q_product t node w 0 d = 0 := by
  simp [b65q_product, b65q_principal]

/-- The frame products `D_θ q_bᵀ r_a` along the path.
Source: G32 v0.16, §5.5(7). -/
def b65q_frameProduct (p : Fin 12 → ℂ)
    (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) (a b : Fin 3) :
    RatFunc ℂ :=
  b65q_product (b65p_poles p θ) p (b65q_left R θ) (fun i ↦ b65q_rFrame p R θ i a)
    (fun i ↦ b65q_qFrame p R θ i b)

example (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ)
    (a b : Fin 3) : b65q_frameProduct p R θ a b =
      b65q_product (b65p_poles p θ) p (b65q_left R θ) (fun i ↦ b65q_rFrame p R θ i a)
        (fun i ↦ b65q_qFrame p R θ i b) := rfl

/-- **The family numerator array** `𝐌(θ)`: row `finProdFinEquiv (a, b) = 3a + b` lists the
coefficients of `s⁰, …, s⁹` of the reduced numerator of `D_θ q_bᵀ r_a`.
Source: G32 v0.16, §5.5(7), the matrix 𝐌(θ); `b65k_baseMatrix`. -/
def b65q_numMatrix (p : Fin 12 → ℂ)
    (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) :
    Matrix (Fin 9) (Fin 10) ℂ := fun i j ↦
  (b65q_frameProduct p R θ ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1
    ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2).num.coeff j.val

example (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ)
    (a b : Fin 3) (j : Fin 10) : b65q_numMatrix p R θ (finProdFinEquiv (a, b)) j =
      (b65q_frameProduct p R θ a b).num.coeff j.val := by
  simp only [b65q_numMatrix, Equiv.symm_apply_apply]

/-- The value of a rational function at a complex point (junk value `0` at a pole).
Source: Mathlib `RatFunc.eval`. -/
def b65q_eval (f : RatFunc ℂ) (s : ℂ) : ℂ := f.eval (RingHom.id ℂ) s

example (s : ℂ) : b65q_eval 0 s = 0 := by simp [b65q_eval]

/-- **The r-space of the dictionary** at one parameter, for a gauge `H k` at each fixed pole:
rational vectors `r` holomorphic off the poles and at the moving poles, with
`ord_{t_k} [(P_k H_k)⁻¹ r]_j ≥ ⌊λ_{k,j}⌋` at the fixed poles, and `ord_∞ r ≥ 2`.
At a moving pole the exponents are `0, 0, 0, λ` with `0 < λ < 1`, and the condition
`ord ≥ ⌊·⌋ = 0` is holomorphy of `r`.
Source: G32 v0.16, Lemma 5.3 (dictionary), order conditions for r. -/
def b65q_rSpace (t : Fin 4 ⊕ Fin 12 → ℂ) (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ) : Set (Fin 4 → RatFunc ℂ) :=
  {r | (∀ i s, (r i).denom.eval s = 0 → s ∈ Set.range t) ∧
    (∀ x : Fin 12, ∀ i, (r i).denom.eval (t (Sum.inr x)) ≠ 0) ∧
    (∀ k j : Fin 4, ((⌊(b65p_exponents k j).re⌋ : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun s ↦ ((P k * H k s)⁻¹ *ᵥ fun i ↦ b65q_eval (r i) s) j)
        (t (Sum.inl k))) ∧
    (∀ i, r i = 0 ∨ (r i).intDegree ≤ -2)}

example (t : Fin 4 ⊕ Fin 12 → ℂ) (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ) : (fun _ ↦ 1) ∉ b65q_rSpace t P H := by
  rintro ⟨-, -, -, h⟩
  rcases h 0 with h | h <;> simp at h

/-- **The q-space of the dictionary** at one parameter: rational vectors `q` holomorphic off the
poles, with `ord_{t_k} [(P_k H_k)ᵀ q]_j ≥ ⌊−λ_{k,j}⌋` at the fixed poles, at most a simple pole
at each moving pole whose pairing with every `0`-eigenvector of the residue there is
holomorphic, and `ord_∞ q ≥ 2`. At a moving pole this is the condition
`ord ≥ ⌊−λ⌋` for the exponents `0, 0, 0, λ`, `0 < λ < 1`.
Source: G32 v0.16, Lemma 5.3 (dictionary), order conditions for q; §5.5(4). -/
def b65q_qSpace (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ) :
    Set (Fin 4 → RatFunc ℂ) :=
  {q | (∀ i s, (q i).denom.eval s = 0 → s ∈ Set.range t) ∧
    (∀ x : Fin 12, ∀ i, (-1 : WithTop ℤ) ≤
      meromorphicOrderAt (fun s ↦ b65q_eval (q i) s) (t (Sum.inr x))) ∧
    (∀ x : Fin 12, ∀ v, A (Sum.inr x) *ᵥ v = 0 → (0 : WithTop ℤ) ≤
      meromorphicOrderAt (fun s ↦ v ⬝ᵥ fun i ↦ b65q_eval (q i) s) (t (Sum.inr x))) ∧
    (∀ k j : Fin 4, ((⌊(-b65p_exponents k j).re⌋ : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun s ↦ ((P k * H k s)ᵀ *ᵥ fun i ↦ b65q_eval (q i) s) j)
        (t (Sum.inl k))) ∧
    (∀ i, q i = 0 ∨ (q i).intDegree ≤ -2)}

example (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ) :
    (fun _ ↦ 1) ∉ b65q_qSpace t A P H := by
  rintro ⟨-, -, -, -, h⟩
  rcases h 0 with h | h <;> simp at h

/-- The map from rational to complex functions, coefficientwise.
Source: Mathlib `RatFunc.mapRingHom`, `Polynomial.map_injective`. -/
def b65q_castRat : RatFunc ℚ →+* RatFunc ℂ :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (Rat.castHom ℂ))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (Rat.castHom ℂ).injective))

example : b65q_castRat 1 = 1 := map_one _

end HodgeLean.Foundations.Program

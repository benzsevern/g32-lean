import HodgeLean.Foundations.Program.KernelFramesFamilyRoots

/-! # B6-5 stage 5d, family part: rational mirror of the systems at the base parameter

Rational copies of the residues, Taylor coefficients, normal-form gauge, inverse series and
Laurent systems of `KernelFramesFamilyDefs.lean`, with the sums over the labels of a fibre
replaced by the rational root sums of `KernelFramesFamilyRoots.lean` and the inverse of the
printed eigenbasis given explicitly. The kernel evaluates them to the printed systems
`b65k_rSystem` and `b65k_qSystem`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

/-- `B₀` over `ℚ`. -/
def b65q_B0Q : Matrix (Fin 4) (Fin 4) ℚ := diagonal ![-3/4, -1/2, -1/2, 3/4]

/-- `u₁`, `u₂` over `ℚ`. -/
def b65q_uQ : Fin 2 → Fin 4 → ℚ := ![![1, 1, 0, 1], ![-5598720/14161, 0, 1, 5598720/22253]]

/-- `B₅ = u₁v₁ᵀ` and `B₋₇ = u₂v₂ᵀ` over `ℚ`. -/
def b65q_BQ (e : Fin 2) : Matrix (Fin 4) (Fin 4) ℚ := Matrix.of fun i j ↦ b65q_uQ e i * b65k_left e j

/-- `B_∞` over `ℚ`. -/
def b65q_BinfQ : Matrix (Fin 4) (Fin 4) ℚ := -(b65q_B0Q + b65q_BQ 0 + b65q_BQ 1)

/-- The fixed-pole residues over `ℚ`. -/
def b65q_fixedResQ : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![(2 : ℚ) • b65q_B0Q, (4 : ℚ) • b65q_B0Q, (3 : ℚ) • b65q_BinfQ, (3 : ℚ) • b65q_BinfQ]

/-- The fixed-pole exponents over `ℚ`. -/
def b65q_lamQ : Fin 4 → Fin 4 → ℚ :=
  ![![-3/2, -1, -1, 3/2], ![-3, -2, -2, 3], ![-2, -2, 2, 2], ![-2, -2, 2, 2]]

/-- The printed eigenbasis at `1, −2` over `ℚ`, and its inverse. -/
def b65q_EQ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 1, 0;
     0, 1, 0, 1;
     -34391/11197440, 14161/5598720, 14161/11197440, 14161/5598720;
     119/11, -252/11, 7/187, 36/187]

def b65q_EinvQ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![7/24, 7/12, -466560/2023, 0;
     119/864, 101/360, -31104/289, -187/4320;
     17/24, -7/12, 466560/2023, 0;
     -119/864, 259/360, 31104/289, 187/4320]

theorem b65q_EQ_mul_inv : b65q_EQ * b65q_EinvQ = 1 := by decide +kernel

/-- The initial eigenbases over `ℚ` and their inverses. -/
def b65q_P0Q : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![1, 1, b65q_EQ, b65q_EQ]

def b65q_P0invQ : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![1, 1, b65q_EinvQ, b65q_EinvQ]

/-- The Taylor coefficients at the fixed pole `k` of the regular part at `θ = 0`. -/
def b65q_TQ (k : Fin 4) (l : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  (∑ k' : Fin 4, if k' = k then 0 else
      (-((b65k_fixed k' - b65k_fixed k) ^ (l + 1))⁻¹) • b65q_fixedResQ k') +
    (-b65q_DQ 0 k (l + 1) 0) • b65q_BQ 0 + (-b65q_DQ 1 k (l + 1) 0) • b65q_BQ 1

/-- The rational normal-form gauge recursion. -/
def b65q_gaugeQ (T : ℕ → Matrix (Fin 4) (Fin 4) ℚ) (P Pinv : Matrix (Fin 4) (Fin 4) ℚ)
    (lam : Fin 4 → ℚ) : ℕ → ℕ → Matrix (Fin 4) (Fin 4) ℚ
  | 0 => fun m ↦ if m = 0 then 1 else 0
  | N + 1 => Function.update (b65q_gaugeQ T P Pinv lam N) (N + 1)
      (Matrix.of fun i j ↦
        if ((N + 1 : ℕ) : ℚ) + lam j - lam i = 0 then 0 else
          (∑ l ∈ Finset.range (N + 1),
              (Pinv * T l * P) * b65q_gaugeQ T P Pinv lam N (N - l)) i j /
            (((N + 1 : ℕ) : ℚ) + lam j - lam i))

/-- The rational inverse-series recursion. -/
def b65q_seriesInvQ (H : ℕ → Matrix (Fin 4) (Fin 4) ℚ) : ℕ → ℕ → Matrix (Fin 4) (Fin 4) ℚ
  | 0 => fun m ↦ if m = 0 then 1 else 0
  | N + 1 => Function.update (b65q_seriesInvQ H N) (N + 1)
      (-∑ m ∈ Finset.range (N + 1), H (m + 1) * b65q_seriesInvQ H N (N - m))

/-- The gauge coefficients at `θ = 0`. -/
def b65q_HQ (k : Fin 4) (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  b65q_gaugeQ (b65q_TQ k) (b65q_P0Q k) (b65q_P0invQ k) (b65q_lamQ k) n n

/-- The r- and q-coefficients at `θ = 0`. -/
def b65q_rCQ (k : Fin 4) (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  b65q_seriesInvQ (b65q_HQ k) n n * b65q_P0invQ k

def b65q_qCQ (k : Fin 4) (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := (b65q_P0Q k * b65q_HQ k n)ᵀ

/-- The rational principal-part entry. -/
def b65q_principalEntryQ (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℚ)
    (k j : Fin 4) (n : ℤ) (c : Fin 36) : ℚ :=
  if b65k_poleIndex ⟨c.val / 4, by omega⟩ = k then
    (if 0 ≤ n + b65k_poleOrder ⟨c.val / 4, by omega⟩ then
      K k (n + b65k_poleOrder ⟨c.val / 4, by omega⟩).toNat j ⟨c.val % 4, by omega⟩ else 0)
  else if 0 ≤ n then
    ∑ l ∈ Finset.range (n.toNat + 1), K k (n.toNat - l) j ⟨c.val % 4, by omega⟩ *
      ((-1) ^ l * ((b65k_poleOrder ⟨c.val / 4, by omega⟩ + l - 1).choose l : ℚ) *
        ((b65k_fixed k - b65k_fixed (b65k_poleIndex ⟨c.val / 4, by omega⟩)) ^
          (b65k_poleOrder ⟨c.val / 4, by omega⟩ + l))⁻¹)
  else 0

/-- The rational infinity entry. -/
def b65q_infinityEntryQ (i : Fin 4) (c : Fin 36) : ℚ :=
  if b65k_poleOrder ⟨c.val / 4, by omega⟩ = 1 ∧ c.val % 4 = i.val then 1 else 0

/-- The rational r-system. -/
def b65q_rSystemQ (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℚ) : Matrix (Fin 45) (Fin 36) ℚ :=
  fun r c ↦
  if h : r.val < 41 then
    b65q_principalEntryQ K (b65q_rRow ⟨r.val, h⟩).1
      (b65q_rRow ⟨r.val, h⟩).2.1 (b65q_rRow ⟨r.val, h⟩).2.2 c
  else b65q_infinityEntryQ ⟨r.val - 41, by omega⟩ c

/-- The rational beta entry at `θ = 0`. -/
def b65q_betaEntryQ (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℚ) (k j : Fin 4) (n : ℤ)
    (e : Fin 2) (v : Fin 6) : ℚ :=
  if 0 ≤ n then
    ∑ l ∈ Finset.range (n.toNat + 1),
      (K k (n.toNat - l) *ᵥ b65k_left e) j * (-b65q_DQ e k (l + 1) v.val)
  else 0

/-- The rational beta entry at `∞` at `θ = 0`. -/
def b65q_betaInfinityQ (i : Fin 4) (e : Fin 2) (v : Fin 6) : ℚ :=
  b65q_psumQ e v * b65k_left e i

/-- The rational q-system. -/
def b65q_qSystemQ (K : Fin 4 → ℕ → Matrix (Fin 4) (Fin 4) ℚ) : Matrix (Fin 57) (Fin 48) ℚ :=
  fun r c ↦
  if h : r.val < 53 then
    if hc : c.val < 36 then
      b65q_principalEntryQ K (b65q_qRow ⟨r.val, h⟩).1
        (b65q_qRow ⟨r.val, h⟩).2.1 (b65q_qRow ⟨r.val, h⟩).2.2 ⟨c.val, hc⟩
    else
      b65q_betaEntryQ K (b65q_qRow ⟨r.val, h⟩).1
        (b65q_qRow ⟨r.val, h⟩).2.1 (b65q_qRow ⟨r.val, h⟩).2.2 ⟨(c.val - 36) / 6, by omega⟩
        ⟨(c.val - 36) % 6, by omega⟩
  else
    if hc : c.val < 36 then b65q_infinityEntryQ ⟨r.val - 53, by omega⟩ ⟨c.val, hc⟩
    else b65q_betaInfinityQ ⟨r.val - 53, by omega⟩ ⟨(c.val - 36) / 6, by omega⟩
      ⟨(c.val - 36) % 6, by omega⟩

set_option maxHeartbeats 400000 in
/-- **Kernel evaluation.** The rational mirror of the r-system is the printed system. -/
theorem b65q_rSystemQ_eq : b65q_rSystemQ b65q_rCQ = b65k_rSystem := by decide +kernel

set_option maxHeartbeats 400000 in
/-- **Kernel evaluation.** The rational mirror of the q-system is the printed system. -/
theorem b65q_qSystemQ_eq : b65q_qSystemQ b65q_qCQ = b65k_qSystem := by decide +kernel

end HodgeLean.Foundations.Program

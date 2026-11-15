import HodgeLean.Foundations.Program.NumeratorJetLaurent
import HodgeLean.Foundations.Program.NumeratorJetBranchData
import HodgeLean.Foundations.Program.NumeratorJetMomentData
import HodgeLean.Foundations.Program.NumeratorJetProductData

/-! # Rational recursions for the numerator jets

Finite rational formulas for the moving-power coordinates, the branch-polynomial jets (Newton
identities), the moving moments, the polynomial parts of `D_θ q` and the numerator jets. The
stored tables are checked against these formulas in the certificate modules.
-/

namespace HodgeLean.Foundations.Program

/-- Coordinates of the root `x` in the sextic quotient. -/
def b65e_rootCoordQ : Fin 6 → ℚ := ![0, 1, 0, 0, 0, 0]

/-- Coordinates of `1`. -/
def b65e_oneCoordQ : Fin 6 → ℚ := ![1, 0, 0, 0, 0, 0]

/-- Moving-power coordinates with natural-number indices (zero outside the table). -/
def b65e_TcN (e : Fin 2) (m n : ℕ) : Fin 6 → ℚ :=
  if h : m < 13 then if h' : n < 8 then b65e_TcQ e ⟨m, h⟩ ⟨n, h'⟩ else 0 else 0

/-- Recursion for the moving-power coordinates: `t^{m+1} = x · t^m + θ V(x) · t^m`. -/
def b65e_TcStepQ (e : Fin 2) (m n : ℕ) (c : Fin 6) : ℚ :=
  b65e_coordinateMulQ e b65e_rootCoordQ (b65e_TcN e m n) c +
    (if n = 0 then 0 else b65e_coordinateMulQ e (b65e_velocityQ e) (b65e_TcN e m (n - 1)) c)

/-- Taylor coefficients of the traced power sums `Σ_x t_x(θ)^b` over both fibres. -/
def b65e_powerTraceQ (b n : ℕ) : ℚ :=
  ∑ e : Fin 2, ∑ c : Fin 6, b65e_TcN e b n c * b65q_psumQ e c

/-- Elementary symmetric jets with natural-number indices. -/
def b65e_esymN (k n : ℕ) : ℚ :=
  if h : k < 13 then if h' : n < 8 then b65e_esymQ ⟨k, h⟩ ⟨n, h'⟩ else 0 else 0

/-- Right side of the Newton identity for the negated poles, order `n`. -/
def b65e_newtonQ (k n : ℕ) : ℚ :=
  (-1) ^ (k + 1) * ∑ a ∈ Finset.range k, (-1) ^ a * ∑ r ∈ Finset.range (n + 1),
    b65e_esymN a r * ((-1) ^ (k - a) * b65e_powerTraceQ (k - a) (n - r))

/-- Taylor coefficients of the coefficient `i` of the branch polynomial `D_θ`. -/
def b65e_DjQ (i n : ℕ) : ℚ := if 1 ≤ i ∧ i ≤ 13 then b65e_esymN (13 - i) n else 0

/-- Formula for the moving-moment coordinates. -/
def b65e_WTFormulaQ (e : Fin 2) (jj : Fin 4) (m n : ℕ) (c : Fin 6) : ℚ :=
  ∑ a ∈ Finset.range (n + 1), b65e_coordinateMulQ e (b65e_leftCoordsQ e jj (Fin.ofNat 8 a))
    (b65e_TcN e m (n - a)) c

/-- Moving-moment coordinates with natural-number indices. -/
def b65e_WTN (e : Fin 2) (jj : Fin 4) (m n : ℕ) : Fin 6 → ℚ :=
  if h : m < 13 then if h' : n < 8 then b65e_WTQ e jj ⟨m, h⟩ ⟨n, h'⟩ else 0 else 0

/-- Formula for the traced moving moments of a q-frame column. -/
def b65e_SqFormulaQ (m : ℕ) (jj : Fin 4) (b : Fin 3) (n : ℕ) : ℚ :=
  ∑ e : Fin 2, ∑ v : Fin 6, ∑ r ∈ Finset.range (n + 1),
    b65e_qFrameJet (Fin.ofNat 8 r) ⟨36 + 6 * e.val + v.val, by omega⟩ b *
      ∑ c : Fin 6, b65e_WTN e jj m (n - r) c * b65e_powerMomentQ ⟨c.val + v.val, by omega⟩ e

/-- Moving moments with natural-number indices. -/
def b65e_SqN (m : ℕ) (jj : Fin 4) (b : Fin 3) (n : ℕ) : ℚ :=
  if h : m < 13 then if h' : n < 8 then b65e_SqQ ⟨m, h⟩ jj b ⟨n, h'⟩ else 0 else 0

/-- Formula for the Taylor coefficients of the coefficient `k` of the polynomial part of
`D_θ q_{jj}` for the q-frame column `b`. -/
def b65e_GFormulaQ (k : ℕ) (jj : Fin 4) (b : Fin 3) (n : ℕ) : ℚ :=
  (∑ b' : Fin 9, ∑ r ∈ Finset.range (n + 1),
    b65e_qFrameJet (Fin.ofNat 8 r) ⟨4 * b'.val + jj.val, by omega⟩ b *
      ∑ i ∈ Finset.range 14, b65e_DjQ i (n - r) * b65e_LamQ b' i k) +
  ∑ m ∈ Finset.range (13 - k), ∑ r ∈ Finset.range (n + 1),
    b65e_DjQ (k + 1 + m) r * b65e_SqN m jj b (n - r)

/-- Polynomial-part coefficients with natural-number indices. -/
def b65e_GN (k : ℕ) (jj : Fin 4) (b : Fin 3) (n : ℕ) : ℚ :=
  if h : k < 13 then if h' : n < 8 then b65e_GQ ⟨k, h⟩ jj b ⟨n, h'⟩ else 0 else 0

/-- Formula for the numerator jets. -/
def b65e_NFormulaQ (n : ℕ) (a b : Fin 3) (j : ℕ) : ℚ :=
  ∑ jj : Fin 4, ∑ k ∈ Finset.range 13, ∑ r ∈ Finset.range (n + 1),
    (∑ a' : Fin 9, b65e_LamQ a' k j *
      b65e_rFrameJet (Fin.ofNat 8 r) ⟨4 * a'.val + jj.val, by omega⟩ a) *
    b65e_GN k jj b (n - r)

end HodgeLean.Foundations.Program

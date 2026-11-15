import HodgeLean.Foundations.Program.KernelFramesFamilyDefs
import HodgeLean.Foundations.Program.NumeratorJetData

/-! # B6-5 stage 5e: the analytic numerator array along the 5c path (definitions)

The residue jets of the 5c record in the rational data of `NumeratorJetData.lean` (fixed poles:
rational matrices; moving poles: polynomials of degree at most five in the labelled root), the
polynomial part of a rational function, and the numerator array `b65e_numerator`: row `3a + b`
lists the coefficients of `s⁰, …, s⁹` of the polynomial part of the 5d frame product
`D_θ q_bᵀ r_a` (`b65q_frameProduct`). Where that product is a polynomial the array is the 5d array
`b65q_numMatrix` (checked below); unlike the reduced numerator, the polynomial part does not
jump where the product acquires a denominator. No statement is asserted here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The order-`n` Taylor coefficient, as listed in the data, of the residue at the pole `q` of a
5c record with labelled roots `p`: the rational matrix `b65e_fixedJet n k` at the fixed pole `k`,
and `Σ_c (p j)^c · b65e_movingJet n e c` at the moving pole `j` over the fibre `e`.
Source: G32 v0.16, §5.5(1) (rationality of the Taylor coefficients through traces over
`E₅ ⊗ E₋₇`) and Lemma 5.6; `NumeratorJetData.lean`. -/
def b65e_residueJet (p : Fin 12 → ℂ) (n : Fin 8) :
    Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ
  | Sum.inl k => (b65e_fixedJet n k).map (Rat.castHom ℂ)
  | Sum.inr j => ∑ c : Fin 6,
      p j ^ c.val • (b65e_movingJet n (b65q_fibreIndex j) c).map (Rat.castHom ℂ)

/-- At order zero the residue jet at the fixed pole `0` is `2B₀ = diag(−3/2, −1, −1, 3/2)`. -/
example (p : Fin 12 → ℂ) : b65e_residueJet p 0 (Sum.inl 0) 0 0 = -3 / 2 := by
  rw [b65e_residueJet, Matrix.map_apply]
  norm_num [b65e_fixedJet, b65e_fixedJet0]

/-- **Non-degeneracy.** The order-one jet at the fixed pole `3` is not zero: the residues move. -/
example : b65e_fixedJet 1 1 0 1 ≠ 0 := by
  simp [b65e_fixedJet, b65e_fixedJet1]

/-- The polynomial part of a rational function: the quotient of its numerator by its monic
denominator. It does not depend on the representation `a / b` with `b` monic.
Source: Mathlib `Polynomial.divByMonic`, `RatFunc.num`, `RatFunc.denom`, `RatFunc.monic_denom`. -/
def b65e_polyPart (f : RatFunc ℂ) : ℂ[X] := f.num /ₘ f.denom

/-- The polynomial part of a polynomial is itself. -/
example (P : ℂ[X]) : b65e_polyPart (algebraMap ℂ[X] (RatFunc ℂ) P) = P := by
  simp [b65e_polyPart]

/-- With denominator one, the polynomial part is the numerator. -/
example (f : RatFunc ℂ) (h : f.denom = 1) : b65e_polyPart f = f.num := by
  simp [b65e_polyPart, h]

/-- **The analytic numerator array** `N(θ)` along a residue path: row `finProdFinEquiv (a, b) =
3a + b` lists the coefficients of `s⁰, …, s⁹` of the polynomial part of the frame product
`D_θ q_bᵀ r_a`.
Source: G32 v0.16, §5.5(7) (the matrix 𝐌(θ) of the products in numerator coordinates),
Lemma 5.5 (numerators), Lemma 5.8 (jets); `b65q_frameProduct`, `b65q_numMatrix`. -/
def b65e_numerator (p : Fin 12 → ℂ)
    (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) :
    Matrix (Fin 9) (Fin 10) ℂ := fun i j ↦
  (b65e_polyPart (b65q_frameProduct p R θ ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1
    ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2)).coeff j.val

/-- **Coupling with 5d.** At every parameter where the nine frame products are polynomials, the
analytic array is the 5d array `b65q_numMatrix` of the same path and residues. -/
example (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ)
    (h : ∀ a b, (b65q_frameProduct p R θ a b).denom = 1) :
    b65e_numerator p R θ = b65q_numMatrix p R θ := by
  ext i j
  simp [b65e_numerator, b65q_numMatrix, b65e_polyPart, h]

end HodgeLean.Foundations.Program

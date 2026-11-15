import HodgeLean.Foundations.Program.SchoenCycleSumPolynomialBlocks
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Independent block invariance splits into symmetry in the first block and invariance of the remaining polynomial coefficients.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
theorem s2e_sum_block_invariants_iff
    {R σ τ G : Type*} [CommRing R] [Group G]
    (t : G →* Equiv.Perm τ) (p : MvPolynomial (σ ⊕ τ) R) :
    (∀ (ρ : Equiv.Perm σ) (g : G), rename (Sum.map ρ (t g)) p = p) ↔
      (sumAlgEquiv R σ τ p).IsSymmetric ∧
        ∀ g : G, map (rename (t g)).toRingHom (sumAlgEquiv R σ τ p) =
          sumAlgEquiv R σ τ p := by
  let q := sumAlgEquiv R σ τ p
  have hmapid : map (rename (id : τ → τ)).toRingHom q = q := by
    apply MvPolynomial.ext
    intro d
    rw [coeff_map]
    exact rename_id_apply _
  constructor
  · intro h
    constructor
    · intro ρ
      have hh := congrArg (sumAlgEquiv R σ τ) (h ρ 1)
      rw [s2e_sum_polynomial_rename_blocks, map_one] at hh
      change rename ρ (map (rename (id : τ → τ)).toRingHom q) = q at hh
      rwa [hmapid] at hh
    · intro g
      have hh := congrArg (sumAlgEquiv R σ τ) (h 1 g)
      rw [s2e_sum_polynomial_rename_blocks] at hh
      change rename (id : σ → σ) (map (rename (t g)).toRingHom q) = q at hh
      rwa [rename_id_apply] at hh
  · rintro ⟨hsym, hcoef⟩ ρ g
    apply (sumAlgEquiv R σ τ).injective
    rw [s2e_sum_polynomial_rename_blocks, hcoef]
    exact hsym ρ

end HodgeLean.Foundations.Program

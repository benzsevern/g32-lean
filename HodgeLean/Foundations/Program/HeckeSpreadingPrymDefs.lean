import HodgeLean.Foundations.Program.HeckeSpreading
import HodgeLean.Papers.G32Assembly

/-! # Hecke spreading S7 on the Prym fibres: definitions

The dominance pairs of a Prym family into the concrete universal family `b60b_univ`, and the
Weil-algebraic locus of `b60b_univ` in `g32m_Domain`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- **Dominance pairs** of a Prym family into the concrete universal family: the pairs `(m, s)`
with a `K`-linear polarized isogeny from the Prym fibre over `s` to `b60b_univ m`. These are the
pairs that `g32r_dominant` produces over its open set.
Source: G32 v0.16, Corollary 5.11 and the first paragraph of the proof of Theorem 7.2 (the
isogeny `N₁ m : A_ρ(C) → A_z`); `g32t_KIsog`. -/
def hk7_pairs (P : g32h_PrymFamily) : Set (g32m_Domain × P.S) :=
  {p | g32t_KIsog (P.fiber p.2) (b60b_univ p.1)}

example (P : g32h_PrymFamily) (m : g32m_Domain) (s : P.S) :
    (m, s) ∈ hk7_pairs P ↔ g32t_KIsog (P.fiber s) (b60b_univ m) := by
  simp only [hk7_pairs, Set.mem_ofPred_eq]

/-- **The Weil-algebraic locus** of the concrete universal family: the points of `𝓗₃` whose
fibre `b60b_univ m` has algebraic Weil classes. It is the left side of the field `spread` of
`g32a_premises` when `F.univ = b60b_univ`.
Source: G32 v0.16, Lemma 7.1 (the locus `𝓜^alg`); `g32t_WeilAlg`. -/
def hk7_algLocus : Set g32m_Domain :=
  {m | g32t_WeilAlg (b60b_univ m)}

example (m : g32m_Domain) : m ∈ hk7_algLocus ↔ g32t_WeilAlg (b60b_univ m) := by
  simp only [hk7_algLocus, Set.mem_ofPred_eq]

end HodgeLean.Foundations.Program

import HodgeLean.Papers.G32ModuliProofs

/-! # G32 Theorem A, stage 1: the Weil-moduli interface (FROZEN SPEC)

Stage 1 of the premise-first route to G32 v0.16 Theorem A: the period domain `𝓗₃` of `SU(3,3)`
as a concrete subset of `ℂ⁹`, the universal family over it as the named premise
`g32m_UniversalFamily`, and the bridge `g32m_transferFields` into `G32TransferDatum`.

Claimed:
* the bounded realization `g32m_periodSet = {Z ∈ M₃(ℂ) | 1 - Zᴴ Z > 0}` is open, convex and
  bounded in `ℂ⁹`, contains `0` and omits the identity matrix;
* `g32m_Domain`, the period domain as an open subset of `ℂ⁹`, is `g32m_periodSet` itself and is
  connected, so it carries every structure that `G32TransferDatum.M` asks for;
* from a universal family: each fibre is a polarized sixfold of Weil type with discriminant
  `[-2]`, and a member of `M = (3, ℚ(√-3), [-2])` exists;
* `g32m_theoremA_of_stages`: the implication from a universal family and the remaining stage
  fields to `G32TheoremAStatement A W pol`, through `g32m_transferFields` and
  `g32t_theoremA_of_transfer`.

Not claimed: the universal family itself (van Geemen's construction of the abelian varieties over
`𝓗₃` and Landherr's theorem are the premise `g32m_UniversalFamily`), and any of the stage fields
`g32m_StageFields` (Hurwitz family, Schoen and Milne suppliers, dominance, discriminant, Hilbert
spreading, isogeny transport). No universal family is constructed, so Theorem A itself remains
unasserted. The base is `𝓗₃`, not the quotient `Γ(ℓ)\𝓗₃`, and the family structure of the fibres
(abelian schemes, variation of Hodge structure) is not recorded.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff ComplexOrder Matrix
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

section Domain

/-- **The period domain is open.** `1 - Zᴴ Z` is positive definite exactly when `‖Z x‖ < ‖x‖`
for every nonzero `x ∈ ℂ³`; by compactness of the unit sphere this is a strict bound on the
operator norm, which is an open condition.
Source: G32 v0.16, Subsection 2.1 (`𝓗_n` is a domain); Hua, *Harmonic Analysis of Functions of
Several Complex Variables in the Classical Domains*, Transl. Math. Monographs 6, AMS (1963),
Introduction (the domain `ℜ_I(m, n)`). -/
theorem g32m_periodSet_isOpen : IsOpen g32m_periodSet :=
  g32m_periodSet_isOpen_aux

example : interior g32m_periodSet = g32m_periodSet :=
  g32m_periodSet_isOpen.interior_eq

/-- **The open subset `g32m_Domain` is the period domain itself**: the interior in its
definition changes nothing.
Source: `g32m_periodSet_isOpen`. -/
theorem g32m_domain_coe : (g32m_Domain : Set (Fin 9 → ℂ)) = g32m_periodSet :=
  g32m_domain_coe_aux

example (z : Fin 9 → ℂ) (hz : z ∈ g32m_periodSet) : z ∈ g32m_Domain := by
  change z ∈ (g32m_Domain : Set (Fin 9 → ℂ))
  rw [g32m_domain_coe]
  exact hz

/-- **The period domain is convex**: if `‖Z x‖ < ‖x‖` and `‖W x‖ < ‖x‖`, then
`‖(t Z + (1 - t) W) x‖ < ‖x‖` for `t ∈ [0, 1]`, by the triangle inequality.
Source: Hua, Transl. Math. Monographs 6 (1963), Introduction (`ℜ_I(m, n)` is a convex
circular domain). -/
theorem g32m_periodSet_convex : Convex ℝ g32m_periodSet :=
  g32m_periodSet_convex_aux

example : _root_.IsPreconnected g32m_periodSet := g32m_periodSet_convex.isPreconnected

/-- **The origin `Z = 0` lies in the period domain**: `1 - 0 = 1` is positive definite.
Source: G32 v0.16, Subsection 2.1 (`𝓗_n` is nonempty); the bounded realization. -/
theorem g32m_zero_mem : (0 : Fin 9 → ℂ) ∈ g32m_Domain :=
  g32m_zero_mem_aux

example : (g32m_Domain : Set (Fin 9 → ℂ)).Nonempty := ⟨0, g32m_zero_mem⟩

/-- **The period domain is bounded**: positivity of `1 - Zᴴ Z` on the basis vector `e_j` gives
`∑ᵢ |Z_{ij}|² < 1`, so every coordinate has modulus less than `1`.
Source: Hua, Transl. Math. Monographs 6 (1963), Introduction (the classical domains are
bounded). -/
theorem g32m_periodSet_isBounded : Bornology.IsBounded g32m_periodSet :=
  g32m_periodSet_isBounded_aux

example : Bornology.IsBounded (g32m_Domain : Set (Fin 9 → ℂ)) :=
  g32m_periodSet_isBounded.subset interior_subset

/-- **The identity matrix is not in the period domain**: `1 - 1ᴴ 1 = 0` is not positive
definite. The domain is a proper subset of `M₃(ℂ)`.
Source: the bounded realization (the boundary point `Z = 1`). -/
theorem g32m_not_mem_of_toMat_eq_one (z : Fin 9 → ℂ) (hz : g32m_toMat z = 1) :
    z ∉ g32m_periodSet :=
  g32m_not_mem_of_toMat_eq_one_aux z hz

example : (fun k : Fin 9 => if k = 0 ∨ k = 4 ∨ k = 8 then (1 : ℂ) else 0) ∉ g32m_periodSet :=
  g32m_not_mem_of_toMat_eq_one _ (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g32m_toMat, finProdFinEquiv])

/-- **The period domain is connected**: it is convex and nonempty. Together with Mathlib's
open-subset instances, `g32m_Domain` is a connected Hausdorff analytic manifold charted on
`ℂ⁹`, the structure `G32TransferDatum.M` asks for.
Source: G32 v0.16, Subsection 2.1 (`𝓗_n` is connected of dimension `n²`). -/
theorem g32m_domain_connectedSpace : ConnectedSpace g32m_Domain :=
  g32m_domain_connectedSpace_aux

example : PreconnectedSpace g32m_Domain :=
  haveI := g32m_domain_connectedSpace
  inferInstance

end Domain

section Family

/-- **Each universal fibre is a polarized sixfold of Weil type for `ℚ(√-3)`**, read off the
`member` field through `g32t_isMember_iff`.
Source: G32 v0.16, Subsection 2.1 (a point of `𝓗_n` gives a Hodge structure of Weil type,
polarized by `Tr_{K/ℚ}(H/2ϑ)`); van Geemen, LNM 1594, 5.10. -/
theorem g32m_univ_polarizedWeil (F : g32m_UniversalFamily) (τ : g32m_Domain) :
    g32t_PolarizedWeil (F.univ τ) :=
  g32m_univ_polarizedWeil_aux F τ

example (F : g32m_UniversalFamily) (τ : g32m_Domain) : dim (F.univ τ).X.left = 6 :=
  (g32m_univ_polarizedWeil F τ).dim_eq

/-- **Each universal fibre has Hermitian discriminant `[-2]`**, for any proof of its polarized
Weil type.
Source: G32 v0.16, Subsection 2.1 (the space `(V, H)` has discriminant `𝔡 = -2`); van Geemen,
LNM 1594, Lemma 5.2. -/
theorem g32m_univ_disc (F : g32m_UniversalFamily) (τ : g32m_Domain)
    (h : g32t_PolarizedWeil (F.univ τ)) : g32t_disc h = classNegTwo :=
  g32m_univ_disc_aux F τ h

example (F : g32m_UniversalFamily) (τ : g32m_Domain) :
    g32t_disc (g32m_univ_polarizedWeil F τ) = classNegTwo :=
  g32m_univ_disc F τ _

/-- **A universal family carries a member of `M`**: the fibre over `0 ∈ 𝓗₃`. A universal family
therefore cannot be built from degenerate data.
Source: G32 v0.16, Subsection 2.1; `g32m_zero_mem`. -/
theorem g32m_exists_member (F : g32m_UniversalFamily) : ∃ P, g32t_IsMember P :=
  g32m_exists_member_aux F

example (F : g32m_UniversalFamily) : ∃ P : g32t_Sixfold, dim P.X.left = 6 :=
  (g32m_exists_member F).imp fun _ h => h.dim_eq

/-- **G32 Theorem A from stage 1 and the remaining stage fields.** For a universal family `F`
over `𝓗₃` and the fields `R` that stages 2–6 supply over it, `G32TheoremAStatement A W pol`
holds for every `A` with the five instances, every rational Weil action `W` of `ℚ(√-3)` and every
degree-two class `pol`: `g32m_transferFields F R` is a transfer datum, and
`g32t_theoremA_of_transfer` applies.

This is the implication from the premise and the stage fields; none of them is asserted here.
Source: G32 v0.16, Subsection 2.1, Theorem 7.2 and the proof of Theorem A. -/
theorem g32m_theoremA_of_stages (F : g32m_UniversalFamily) (R : g32m_StageFields F)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32m_theoremA_of_stages_aux F R A W pol

/-- The datum of the bridge, with connectedness supplied by `g32m_domain_connectedSpace`, has
`M = 𝓗₃`, `univ = F.univ` and `cover = F.cover`. -/
example (F : g32m_UniversalFamily) (R : g32m_StageFields F) : G32TransferDatum :=
  haveI := g32m_domain_connectedSpace
  g32m_transferFields F R

end Family

end HodgeLean.Papers

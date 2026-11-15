import HodgeLean.Foundations.Program.G32RepWeil
import HodgeLean.Foundations.Program.G32ContractionGamma

/-!
# Restoration of the Weil character and the `U`-invariance of `Γ` (FROZEN SPEC)

Two of the three statements set aside from `G32Contraction.lean` on 2026-11-05
(`docs/specs/G32Contraction.md`, "Set aside (2026-11-05)"), with exactly their former signatures:

* `g32c_weil_character`: `U` acts on the Weil line `det A.W.Vs ⊆ ⋀⁶ H¹(A; ℂ)` by `e_ρ^ε` for one
  sign `ε`; derived here from the stage H statements `g32rep_weil_preserved`, `g32rep_weil_finrank`
  and `g32rep_weil_sign` (`G32RepWeil.lean`) and `rfd_exteriorPower_map_top`;
* `g32c_gamma_invariant`: the reduction `g32c_gamma_invariant_of` applied to
  `hW := g32c_weil_character X`, `hpar` from `g32rep_parity` and the `θ` clause of the enumeration,
  and `hco := fun j => g32rep_hco X (S j) (hS j) (χc j) (hχc j) τ τbar θ hE`.

Both are implications from the fields of `g32p_Cover` and the frozen statements they cite; this
module adds no open body of its own. The third set-aside statement, `g32c_supplier_character`, is
not restored here. Nothing here asserts that a `g32p_Cover` exists, an algebraicity or a character
comparison. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

/-- **The Weil line carries `e_ρ^ε`.** There is one sign `ε` such that every `u ∈ U` acts on the
Weil line `det A.W.Vs ⊆ ⋀⁶ H¹(A; ℂ)`, through its transport `g32c_restrict X.inclA X.projA X.NA u`,
by `e_ρ(u)^ε`: the transport preserves `A.W.Vs` (`g32rep_weil_preserved`), which has dimension six
(`g32rep_weil_finrank`), so it acts on `⋀⁶ A.W.Vs` by its determinant there
(`rfd_exteriorPower_map_top`), which is `e_ρ(u)^ε` (`g32rep_weil_sign`).
Source: G32 v0.16, proof of Proposition 4.6 (the character of `U` on `W_K(A)`); Lemma 3.6;
`g32rep_weil_preserved`, `g32rep_weil_finrank`, `g32rep_weil_sign`. -/
theorem g32c_weil_character (X : g32p_Cover A) :
    ∃ ε : ℤˣ, ∀ (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X),
      ∀ z ∈ LinearMap.range (exteriorPower.map 6 A.W.Vs.subtype),
        exteriorPower.map 6 (g32c_restrict X.inclA X.projA X.NA u) z =
          g32c_char X g32p_rho u hu ^ (ε : ℤ) • z := by
  have := (torusCohomology_cupProductOf A.X).finite
  obtain ⟨ε, hε⟩ := g32rep_weil_sign X
  refine ⟨ε, fun u hu z hz => ?_⟩
  obtain ⟨w, rfl⟩ := hz
  have hp := g32rep_weil_preserved X hu
  have hcomp : g32c_restrict X.inclA X.projA X.NA u ∘ₗ A.W.Vs.subtype =
      A.W.Vs.subtype ∘ₗ (g32c_restrict X.inclA X.projA X.NA u).restrict hp := rfl
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hcomp, exteriorPower.map_comp,
    LinearMap.comp_apply, rfd_exteriorPower_map_top (g32rep_weil_finrank X), map_smul,
    hε u hu hp]

/-- The Weil line is fixed by every `u ∈ U` with `e_ρ(u) = 1`. -/
example (X : g32p_Cover A) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X)
    (h1 : g32c_char X g32p_rho u hu = 1) :
    ∀ z ∈ LinearMap.range (exteriorPower.map 6 A.W.Vs.subtype),
      exteriorPower.map 6 (g32c_restrict X.inclA X.projA X.NA u) z = z := by
  obtain ⟨ε, hε⟩ := g32c_weil_character X
  intro z hz
  rw [hε u hu z hz, h1, one_zpow, one_smul]

/-- **`Γ` is `U`-invariant.** For a family of admissible suppliers with an identity
`Σ_j ε_j a(χ_j) = e_{iρ}`, there is a sign `δ` such that for embeddings `t_j` with
`t_j(ζ) = exp(2πi/m_j)^{δ ε_j}`, every `u ∈ U` fixes `Γ(w, Z)` for `w` on the Weil line and `Z_j`
on the complementary lines: `g32c_gamma_invariant_of` with `hW := g32c_weil_character X`, `hpar`
from `g32rep_parity` and the `θ` clause of `hE`, and `hco` from `g32rep_hco` for each supplier.
Source: G32 v0.16, proof of Proposition 4.6, paragraphs "The correspondence" and "Degrees";
`g32c_gamma_invariant_of`, `g32c_weil_character`, `g32rep_parity`, `g32rep_hco`. -/
theorem g32c_gamma_invariant (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (χc : ∀ j, (S j).H →* ℂˣ)
    (hχc : ∀ j h, ((χc j h : ℂˣ) : ℂ) =
      g32p_root (S j).m ^ (Multiplicative.toAdd ((S j).χ h)).val)
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ) (iρ : I)
    (hρ : Nonempty (τ iρ ≅ g32p_rho)) (ε : Fin r → ℤˣ)
    (hid : ∑ j, (ε j : ℤ) • papersA τ τbar θ (S j).H (χc j) = (Pi.single iρ 1, 0)) :
    ∃ δ : ℤˣ, ∀ t : ∀ j, cyc_Field (S j).m →ₐ[ℚ] ℂ,
      (∀ j, t j (g32p_zeta (S j)) = g32p_root (S j).m ^ ((δ * ε j : ℤˣ) : ℤ)) →
      ∀ w ∈ LinearMap.range (exteriorPower.map 6 A.W.Vs.subtype),
      ∀ Z : ∀ j, ⋀[ℂ]^(2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1))
          (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1),
      (∀ j, Z j ∈ g32c_coLine (X.part (S j) (hS j)).act.cyc_coordinates (t j)
          (2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1))) →
      ∀ u ∈ g32c_U X,
        g32c_factorAction (g32c_restrict X.inclA X.projA X.NA u)
            (fun j => g32c_restrict (X.part (S j) (hS j)).incl (X.part (S j) (hS j)).proj
              (X.part (S j) (hS j)).N u)
            (g32c_gammaAbs (w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ A.X 1))
              fun j => (Z j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))) =
          g32c_gammaAbs (w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ A.X 1))
            fun j => (Z j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)) :=
  g32c_gamma_invariant_of X S hS χc hχc τ τbar θ hE iρ hρ ε hid (g32c_weil_character X)
    (fun u hu q => g32rep_parity X (θ q) (hE.2.1 q).1 (hE.2.1 q).2.1 u hu)
    (fun j => g32rep_hco X (S j) (hS j) (χc j) (hχc j) τ τbar θ hE)

/-- With no suppliers, the identity `0 = e_{iρ}` is impossible, so the hypotheses of
`g32c_gamma_invariant` cannot hold for `r = 0`. -/
example {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (iρ : I) (S : Fin 0 → g32p_Supplier) (χc : ∀ j, (S j).H →* ℂˣ)
    (ε : Fin 0 → ℤˣ) :
    ∑ j, (ε j : ℤ) • papersA τ τbar θ (S j).H (χc j) ≠ (Pi.single iρ 1, 0) := by
  rw [Finset.univ_eq_empty, Finset.sum_empty]
  intro h
  have := congrFun (congrArg Prod.fst h) iρ
  simp at this

end HodgeLean.Foundations.Program

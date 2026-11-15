import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective

/-! # The Segre embedding over `ℤ`: integral models and charts (FROZEN DEFINITIONS)

The integral projective space `ℙⁿ_ℤ = Proj ℤ[x_0, …, x_n]` (the factor that
`ProjectiveSpace (Fin (n+1)) T` base-changes to `T`), the Segre target
`Proj ℤ[z_{kl} | (k, l) ∈ Fin (n+1) × Fin (m+1)]`, the fibre product `ℙⁿ_ℤ × ℙᵐ_ℤ` over the
terminal scheme, its charts `D₊(x_i) × D₊(y_j)`, and on each chart the Segre map
`z_{kl} ↦ (x_k / x_i)(y_l / y_j)` into the Segre target, built with Mathlib's
`Proj.fromOfGlobalSections`. The glued Segre morphism itself is not defined here: its existence
is a frozen statement of `SegreProjective.lean`.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The integral projective `n`-space `ℙⁿ_ℤ = Proj ℤ[x_0, …, x_n]`, each variable of degree one.
Source: Hartshorne, *Algebraic Geometry*, §II.2 (`Proj`) and §II.7 (`ℙⁿ_ℤ`); upstream
`HodgeConjecture/Definitions/AlgebraicGeometry/ProjectiveSpace.lean` at `2ead713`
(`ProjectiveSpace` is the base change of this scheme), `ComplexProjectiveSpace.UniversalGrading`. -/
abbrev g3c_P (n : ℕ) : Scheme.{0} := Proj (UniversalGrading n)

example (n : ℕ) : g3c_P n = Proj (homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) := rfl

/-- The grading of the Segre target ring `ℤ[z_{kl}]`, `(k, l) ∈ Fin (n+1) × Fin (m+1)`, each
variable of degree one.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.5.11 (the Segre embedding); Mathlib
`MvPolynomial.homogeneousSubmodule`. -/
abbrev g3c_segreGrading (n m : ℕ) :=
  homogeneousSubmodule (Fin (n + 1) × Fin (m + 1)) (ULift.{0} ℤ)

example (n m : ℕ) :
    g3c_segreGrading n m =
      homogeneousSubmodule (Fin (n + 1) × Fin (m + 1)) (ULift.{0} ℤ) := rfl

/-- The Segre target `Proj ℤ[z_{kl}]`, projective space with homogeneous coordinates indexed by
`Fin (n+1) × Fin (m+1)`.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.5.11; Mathlib `AlgebraicGeometry.Proj`. -/
abbrev g3c_segreTarget (n m : ℕ) : Scheme.{0} := Proj (g3c_segreGrading n m)

example (n m : ℕ) : g3c_segreTarget n m = Proj (g3c_segreGrading n m) := rfl

/-- The fibre product `ℙⁿ_ℤ × ℙᵐ_ℤ` over the terminal scheme.
Source: Hartshorne, *Algebraic Geometry*, Thm. II.3.3 (fibre products); Mathlib `pullback`,
`terminal.from`. -/
abbrev g3c_prod (n m : ℕ) : Scheme.{0} :=
  pullback (terminal.from (g3c_P n)) (terminal.from (g3c_P m))

example (n m : ℕ) :
    g3c_prod n m = pullback (terminal.from (g3c_P n)) (terminal.from (g3c_P m)) := rfl

/-- The standard chart `Spec ℤ[x_0/x_i, …, x_n/x_i] = D₊(x_i) ⟶ ℙⁿ_ℤ`.
Source: Hartshorne, *Algebraic Geometry*, Prop. II.2.5(b); Mathlib `Proj.awayι`. -/
def g3c_chartι (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (Away (UniversalGrading n) (X i : UniversalRing n))) ⟶ g3c_P n :=
  Proj.awayι (UniversalGrading n) (X i) (isHomogeneous_X _ i) zero_lt_one

instance g3c_chartι_isOpenImmersion (n : ℕ) (i : Fin (n + 1)) :
    IsOpenImmersion (g3c_chartι n i) := by
  unfold g3c_chartι; infer_instance

example (n : ℕ) (i : Fin (n + 1)) : IsOpenImmersion (g3c_chartι n i) := inferInstance

/-- The chart `D₊(x_i) × D₊(y_j)` of `ℙⁿ_ℤ × ℙᵐ_ℤ`, as a fibre product of two affine schemes
over the terminal scheme.
Source: Hartshorne, *Algebraic Geometry*, Thm. II.3.3, Step 1 (fibre products of affine
schemes); Mathlib `pullback`. -/
abbrev g3c_chart (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) : Scheme.{0} :=
  pullback (terminal.from (Spec (.of (Away (UniversalGrading n) (X i : UniversalRing n)))))
    (terminal.from (Spec (.of (Away (UniversalGrading m) (X j : UniversalRing m)))))

example (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    g3c_chart n m i j =
      pullback (terminal.from (Spec (.of (Away (UniversalGrading n) (X i : UniversalRing n)))))
        (terminal.from (Spec (.of (Away (UniversalGrading m) (X j : UniversalRing m))))) := rfl

/-- The open immersion `D₊(x_i) × D₊(y_j) ⟶ ℙⁿ_ℤ × ℙᵐ_ℤ`.
Source: Hartshorne, *Algebraic Geometry*, Thm. II.3.3, Step 3 (open subschemes of a fibre
product); Mathlib `pullback.map`, `Scheme.pullback_map_isOpenImmersion`. -/
def g3c_prodChartι (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    g3c_chart n m i j ⟶ g3c_prod n m :=
  pullback.map _ _ _ _ (g3c_chartι n i) (g3c_chartι m j) (𝟙 _) (by simp) (by simp)

instance g3c_prodChartι_isOpenImmersion (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    IsOpenImmersion (g3c_prodChartι n m i j) := by
  unfold g3c_prodChartι; infer_instance

example (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    IsOpenImmersion (g3c_prodChartι n m i j) := inferInstance

/-- The regular function `x_k / x_i` of `D₊(x_i)`, pulled back to the chart
`D₊(x_i) × D₊(y_j)` along the first projection.
Source: Hartshorne, *Algebraic Geometry*, Prop. II.2.5(b); `ComplexProjectiveSpace.chartCoordinate`,
Mathlib `Scheme.ΓSpecIso`, `Scheme.Hom.appTop`. -/
def g3c_fstCoord (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) (k : Fin (n + 1)) :
    Γ(g3c_chart n m i j, ⊤) :=
  (Scheme.Hom.appTop (pullback.fst (terminal.from _) (terminal.from _))).hom
    ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate i k))

example (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) (k : Fin (n + 1)) :
    Γ(g3c_chart n m i j, ⊤) :=
  g3c_fstCoord n m i j k

/-- The regular function `y_l / y_j` of `D₊(y_j)`, pulled back to the chart
`D₊(x_i) × D₊(y_j)` along the second projection.
Source: as `g3c_fstCoord`. -/
def g3c_sndCoord (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) (l : Fin (m + 1)) :
    Γ(g3c_chart n m i j, ⊤) :=
  (Scheme.Hom.appTop (pullback.snd (terminal.from _) (terminal.from _))).hom
    ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate j l))

example (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) (l : Fin (m + 1)) :
    Γ(g3c_chart n m i j, ⊤) :=
  g3c_sndCoord n m i j l

/-- The Segre ring map on the chart `D₊(x_i) × D₊(y_j)`: `z_{kl} ↦ (x_k / x_i)(y_l / y_j)`.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.5.11; Mathlib `MvPolynomial.eval₂Hom`. -/
def g3c_chartSections (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    MvPolynomial (Fin (n + 1) × Fin (m + 1)) (ULift.{0} ℤ) →+* Γ(g3c_chart n m i j, ⊤) :=
  eval₂Hom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
    fun kl => g3c_fstCoord n m i j kl.1 * g3c_sndCoord n m i j kl.2

example (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    MvPolynomial (Fin (n + 1) × Fin (m + 1)) (ULift.{0} ℤ) →+* Γ(g3c_chart n m i j, ⊤) :=
  g3c_chartSections n m i j

theorem g3c_chartSections_X (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1))
    (kl : Fin (n + 1) × Fin (m + 1)) :
    g3c_chartSections n m i j (X kl) = g3c_fstCoord n m i j kl.1 * g3c_sndCoord n m i j kl.2 :=
  eval₂Hom_X' _ _ _

theorem g3c_chartSections_X_self (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    g3c_chartSections n m i j (X (i, j)) = 1 := by
  rw [g3c_chartSections_X]
  simp [g3c_fstCoord, g3c_sndCoord, chartCoordinate_self]

theorem g3c_chartSections_irrelevant (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    (HomogeneousIdeal.irrelevant (g3c_segreGrading n m)).toIdeal.map
      (g3c_chartSections n m i j) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ zero_lt_one
      (isHomogeneous_X _ (i, j))))
    (by rw [g3c_chartSections_X_self]; exact isUnit_one)

/-- The Segre map on the chart `D₊(x_i) × D₊(y_j)`, into the Segre target: Mathlib's morphism
to `Proj` from the ring map `z_{kl} ↦ (x_k / x_i)(y_l / y_j)`, whose value at `z_{ij}` is `1`.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.5.11; Mathlib `Proj.fromOfGlobalSections`. -/
def g3c_chartMap (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    g3c_chart n m i j ⟶ g3c_segreTarget n m :=
  Proj.fromOfGlobalSections (g3c_segreGrading n m) (g3c_chartSections n m i j)
    (g3c_chartSections_irrelevant n m i j)

example (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    g3c_chartMap n m i j ⁻¹ᵁ Proj.basicOpen (g3c_segreGrading n m) (X (i, j)) = ⊤ := by
  rw [g3c_chartMap, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ zero_lt_one
    (isHomogeneous_X _ (i, j)), g3c_chartSections_X_self, Scheme.basicOpen_one]

end HodgeLean.Foundations

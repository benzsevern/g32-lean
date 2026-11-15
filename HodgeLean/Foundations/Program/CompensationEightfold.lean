import HodgeLean.Foundations.Program.CompensationEightfoldProofs

/-! # Eightfold compensation, first part of stage C8 (G34 Proposition 10.2)

The frozen spec for `docs/specs/CompensationEightfold.md`. Each theorem is the matching `_aux`
theorem of `CompensationEightfoldProofs.lean`. The stage serves the `hComp` binder of
`g34c_theoremB_of` (`HodgeLean/Papers/G34Compensation.lean:63`), whose conclusion is the exact
inclusion `weilClassOf A ≤ algebraicCycleClassSpan A 3` of line 68.

It claims, for the rational Weil classes `weilClasses` (Blocks) and `weilClassOf` (cohomology):

* **Descent.** For `d > 0` the complex span of the complexified rational Weil classes is the sum
  of the two conjugate top eigenlines `⋀^top Vs ⊔ ⋀^top Vsbar`.
* **Nonzero coefficients.** For a positive-dimensional factor, a nonzero rational Weil class
  has nonzero components on both lines, in every decomposition along them.
* **Rank two.** For an abelian variety of positive dimension, the rational Weil classes in
  `H^(2k)(X; ℚ)` form a rank-two space. This covers `A`, the surface `Y` and the split eightfold
  `A × Y` at once; the eightfold witness `ξ = cq8_weilWitness` is then nonzero (a chain check).
* **The composed surface map.** On `E × Ē` with `J = 1 + 2σ*`, the composite
  `cq8_surfaceEnd2 E ρ` acts on the top line of `Vs` by `(1 + ζ)²` and on that of `Vsbar` by the
  conjugate, and its pullback preserves the rational Weil classes of the surface.
* **Scalar extension.** The normalization `P (a × b) = I(b) a` and the vanishing of `P` on other
  bidegrees, wherever they hold rationally, hold for the complex cross product. Compatibility of
  `cupC`, base changes and conjugation is on `main` (`sigmaQ_cupC`, `sigmaQ_baseChange`) and is
  only used in examples here.

It does not claim: the C5 transport of the eigenlines through Künneth, the geometric surface
square-zero vectors, the existence of `P` and `I` (C7, on `spec/comp2`), the contraction of
`ξ ∪ pr_Y^* y` and its image, or the independence and span conclusion of C8; those are the plan
of the document. Implication from C1–C4 on `main` and from the existing rank-two and injectivity
results of `RationalKernel.lean`. HC no distance; AV milestone no distance.
-/

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Papers
open ComplexConjugate

namespace HodgeLean.Foundations.Program

/-! ### Descent and nonzero coefficients -/

section Descent

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
  {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ}

/-- **Rational descent of the Weil lines.** For `d > 0` the complex span of the complexified
rational Weil classes is `⋀^top Vs ⊔ ⋀^top Vsbar`: the sum of the two lines is defined over
`ℚ(√-d)` and stable under its Galois group, so it descends to `ℚ`.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, LNM 1594,
§4.2 (`W_K ⊗_ℚ K = ⋀^{2n} Z_κ ⊕ ⋀^{2n} Z_κ̄`); Bourbaki, *Algebra*, Chapter V, §10 (Galois
descent). -/
theorem cq8_weilClasses_span (A : HodgeBlocks.WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) (hd : 0 < d) :
    Submodule.span ℂ (HodgeBlocks.complexifyWedge _ '' (A.weilClasses hH hWeil : Set
      (⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
        Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V))) =
      LinearMap.range (exteriorPower.map (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
          Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
          Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) A.Vsbar.subtype) :=
  cq8_weilClasses_span_aux A hH hWeil hd

/-- The span lies in the sum of the lines by the definition of `weilClasses`. -/
example (A : HodgeBlocks.WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) (hd : 0 < d)
    {w : ⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V} (hw : w ∈ A.weilClasses hH hWeil) :
    HodgeBlocks.complexifyWedge _ w ∈
      LinearMap.range (exteriorPower.map _ A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map _ A.Vsbar.subtype) := by
  rw [← cq8_weilClasses_span A hH hWeil hd]
  exact Submodule.subset_span ⟨w, hw, rfl⟩

/-- **Nonzero coefficients along the matched lines.** For a positive-dimensional factor, if a
nonzero rational Weil class complexifies to `x + y` with `x` on `⋀^top Vs` and `y` on
`⋀^top Vsbar`, then `x ≠ 0` and `y ≠ 0`: conjugation fixes the class and exchanges the two lines,
which meet in `0`, and `complexifyWedge` is injective.
Source: G34 v1.5, proof of Proposition 10.2; van Geemen, LNM 1594, §4.2;
`complexifyWedge_injective`, `WeilAction.map_Vs_sigmaQ`. -/
theorem cq8_weilClasses_parts_ne_zero (A : HodgeBlocks.WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) (hd : 0 < d)
    (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
    {w : ⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V}
    (hw : w ∈ A.weilClasses hH hWeil) (hw0 : w ≠ 0)
    {x y : ⋀[ℂ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) (ℂ ⊗[ℚ] V)}
    (hx : x ∈ LinearMap.range (exteriorPower.map _ A.Vs.subtype))
    (hy : y ∈ LinearMap.range (exteriorPower.map _ A.Vsbar.subtype))
    (hxy : HodgeBlocks.complexifyWedge _ w = x + y) :
    x ≠ 0 ∧ y ≠ 0 :=
  cq8_weilClasses_parts_ne_zero_aux A hH hWeil hd hκ hw hw0 hx hy hxy

/-- Chain check: a nonzero rational Weil class has a decomposition along the two lines, and
both of its parts are nonzero. -/
example (A : HodgeBlocks.WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) (hd : 0 < d)
    (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
    {w : ⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V}
    (hw : w ∈ A.weilClasses hH hWeil) (hw0 : w ≠ 0) :
    ∃ x ∈ LinearMap.range (exteriorPower.map _ A.Vs.subtype),
      ∃ y ∈ LinearMap.range (exteriorPower.map _ A.Vsbar.subtype),
        HodgeBlocks.complexifyWedge _ w = x + y ∧ x ≠ 0 ∧ y ≠ 0 := by
  have hmem : HodgeBlocks.complexifyWedge _ w ∈
      LinearMap.range (exteriorPower.map _ A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map _ A.Vsbar.subtype) := hw
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hmem
  exact ⟨x, hx, y, hy, hxy.symm,
    cq8_weilClasses_parts_ne_zero A hH hWeil hd hκ hw hw0 hx hy hxy.symm⟩

end Descent

/-! ### Rank two in cohomology -/

section Rank

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μc : CupProduct X} [GrpObj X]

/-- **Rank two for the rational Weil classes of an abelian variety.** For `d > 0` and
`dim X > 0`, `weilClassOf A hW ⊆ H^(2k)(X; ℚ)` has rank two: `2k = dim X` gives `k ≥ 1`,
`WeilAction.finrank_weilClasses_eq_two` gives rank two in `⋀^(2k) H¹`, and the torus theorem
makes the cup map injective. It applies to `A`, `Y` and the split eightfold `A × Y`.
Source: van Geemen, LNM 1594, §4.2 and Lemma 5.2; Birkenhake–Lange, *Complex Abelian Varieties*,
2nd ed., Lemma 1.3.1 (through `TorusCohomology`); `finrank_weilClasses_eq_two`,
`two_mul_finrank_vs_inf_h10_eq`. -/
theorem cq8_weilClassOf_finrank (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μc) {d : ℚ} (hd : 0 < d)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (hX : 0 < TopologicalSpace.dim X.left) :
    letI := hT.finite
    Module.finrank ℚ ↥(weilClassOf hF hB hD hT A hW) = 2 :=
  cq8_weilClassOf_finrank_aux hF hB hD hT hd A hW hX

/-- Chain check: the eightfold witness `ξ` (and the chosen class on any positive-dimensional
abelian variety) is a nonzero rational Weil class. -/
example (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μc) {d : ℚ} (hd : 0 < d)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (hX : 0 < TopologicalSpace.dim X.left) :
    letI := hT.finite
    cq8_weilWitness hF hB hD hT A hW ∈ weilClassOf hF hB hD hT A hW ∧
      cq8_weilWitness hF hB hD hT A hW ≠ 0 := by
  let := hT.finite
  have h2 := cq8_weilClassOf_finrank hF hB hD hT hd A hW hX
  have hex : ∃ v ∈ weilClassOf hF hB hD hT A hW, v ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot (fun h => by rw [h] at h2; simp at h2)
  unfold cq8_weilWitness
  split_ifs with h
  · exact h.choose_spec
  · exact absurd hex h

/-- Chain check toward `hComp` (`G34Compensation.lean:68`): two linearly independent rational
Weil classes in the algebraic span give `WeilClassesAlgebraic`, by rank two. This is the last
step of the C8 plan. -/
example (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μc) {d : ℚ} (hd : 0 < d)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (hX : 0 < TopologicalSpace.dim X.left)
    (v : Fin 2 → HQ X (2 * Module.finrank ℂ
      ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0))))
    (hv : letI := hT.finite; ∀ i, v i ∈ weilClassOf hF hB hD hT A hW)
    (hvalg : ∀ i, v i ∈ algebraicCycleClassSpan X (Module.finrank ℂ
      ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0))))
    (hind : LinearIndependent ℚ v) :
    WeilClassesAlgebraic hF hB hD hT A hW := by
  let := hT.finite
  have h2 := cq8_weilClassOf_finrank hF hB hD hT hd A hW hX
  have hle : Submodule.span ℚ (Set.range v) ≤ weilClassOf hF hB hD hT A hW :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hv)
  have hfin : FiniteDimensional ℚ ↥(weilClassOf hF hB hD hT A hW) :=
    Module.finite_of_finrank_pos (by omega)
  have heq : Submodule.span ℚ (Set.range v) = weilClassOf hF hB hD hT A hW :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_eq_card hind, h2]; simp)
  intro z hz
  rw [← heq] at hz
  exact (Submodule.span_le.mpr (Set.range_subset_iff.mpr hvalg)) hz

end Rank

/-! ### The composed surface map -/

section Surface

variable (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] [IsIntegral E.left] [Smooth E.hom]
  [IsProjective E.hom]

/-- **The composed surface map on the `Vs` line.** On `E × Ē` with `J = 1 + 2σ*`,
`σ = ρ × ρ²`, the composite `(u, v) ↦ ((1 + ρ)² u, v)` acts on `⋀² Vs` by `(1 + ζ)²`:
`Vs = pr₁^* V_ζ(E) ⊕ pr₂^* V_ζ̄(E)`, the pullback acts by `(1 + ζ)²` on the first summand and by
`1` on the second, and `⋀²` multiplies the two.
Source: G34 v1.5, proof of Proposition 10.2, "Two independent classes"; Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., §1.2 (rational representation); `spec_homPullback_mul`,
`spec_homPullback_comp`. -/
theorem cq8_surfaceEnd2_Vs (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) :
    letI := (finiteBetti_abelian (E ⊗ E)).finite 1
    ∀ x ∈ LinearMap.range (exteriorPower.map 2 W.Vs.subtype),
      exteriorPower.map 2 ((homPullback (cq8_surfaceEnd2 E ρ) 1).baseChange ℂ) x =
        (1 + cp_zeta) ^ 2 • x :=
  cq8_surfaceEnd2_Vs_aux E hE ρ hρ W hJ

example := @cq8_surfaceEnd2_Vs

/-- **The composed surface map on the `Vsbar` line.** The conjugate statement: the composite
acts on `⋀² Vsbar` by `conj ((1 + ζ)²)`.
Source: G34 v1.5, proof of Proposition 10.2, "Two independent classes";
`WeilAction.map_Vs_sigmaQ`, `sigmaQ_baseChange`. -/
theorem cq8_surfaceEnd2_Vsbar (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E)
    [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) :
    letI := (finiteBetti_abelian (E ⊗ E)).finite 1
    ∀ x ∈ LinearMap.range (exteriorPower.map 2 W.Vsbar.subtype),
      exteriorPower.map 2 ((homPullback (cq8_surfaceEnd2 E ρ) 1).baseChange ℂ) x =
        conj ((1 + cp_zeta) ^ 2) • x :=
  cq8_surfaceEnd2_Vsbar_aux E hE ρ hρ W hJ

example := @cq8_surfaceEnd2_Vsbar

/-- **The composed surface map preserves the rational Weil classes.** Its pullback on
`H²(E × Ē; ℚ)` maps `weilClassOf` into itself: it is rational, it is multiplicative on the
image of `⋀² H¹`, and its complexification preserves both lines.
Source: G34 v1.5, proof of Proposition 10.2; Hatcher, *Algebraic Topology*, §3.2 (pullback is a
ring map); `spec_homPullback_cup`. -/
theorem cq8_surfaceEnd2_weilClassOf (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E)
    [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ))
    (hW : letI := (finiteBetti_abelian (E ⊗ E)).finite 1; W.IsWeilType) :
    letI := (finiteBetti_abelian (E ⊗ E)).finite 1
    (weilClassOf (finiteBetti_abelian (E ⊗ E)) (spec_bettiDeRhamIso_abelian (E ⊗ E))
        (hodgeDecomposition_of_abelian (E ⊗ E)) (torusCohomology_cupProductOf (E ⊗ E))
        W hW).map (homPullback (cq8_surfaceEnd2 E ρ) _) ≤
      weilClassOf (finiteBetti_abelian (E ⊗ E)) (spec_bettiDeRhamIso_abelian (E ⊗ E))
        (hodgeDecomposition_of_abelian (E ⊗ E)) (torusCohomology_cupProductOf (E ⊗ E)) W hW :=
  cq8_surfaceEnd2_weilClassOf_aux E hE ρ hρ W hJ hW

example := @cq8_surfaceEnd2_weilClassOf

/-- Instance check, not degenerate: for the actual Weil action of `E × Ē` the surface has
dimension two, `k = 1`, `Vs` has rank two and its top line has rank one, so the eigenvalue
statements quantify over a nonzero line and the rank-two statement applies. -/
example (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) :
    letI := (finiteBetti_abelian (E ⊗ E)).finite 1
    0 < TopologicalSpace.dim (E ⊗ E).left ∧
      Module.finrank ℂ ↥((cp_weilAction (E ⊗ E) (cp_conjAut E ρ)
        (cp_weilOperator_sq _ _ (cp_conjAut_relation E ρ hρ))).Vs ⊓
          (abelianWeightOneHodgeStructure (E ⊗ E)).H (1, 0)) = 1 ∧
      Module.finrank ℂ ↥(LinearMap.range (exteriorPower.map 2
        (cp_weilAction (E ⊗ E) (cp_conjAut E ρ)
          (cp_weilOperator_sq _ _ (cp_conjAut_relation E ρ hρ))).Vs.subtype)) = 1 := by
  let := (finiteBetti_abelian (E ⊗ E)).finite 1
  have hdim : TopologicalSpace.dim (E ⊗ E).left = 2 := by rw [cp_product_dim, hE]
  have hW := cp_cm_surface_weilType E ρ hρ (cp_weilAction (E ⊗ E) (cp_conjAut E ρ)
    (cp_weilOperator_sq _ _ (cp_conjAut_relation E ρ hρ))) rfl
  have h2 := two_mul_finrank_vs_inf_h10_eq (finiteBetti_abelian (E ⊗ E))
    (spec_bettiDeRhamIso_abelian (E ⊗ E)) (hodgeDecomposition_of_abelian (E ⊗ E))
    (torusCohomology_cupProductOf (E ⊗ E)) (by norm_num : (0 : ℚ) < 3) _ hW
  have hk : 2 * Module.finrank ℂ ↥((cp_weilAction (E ⊗ E) (cp_conjAut E ρ)
        (cp_weilOperator_sq _ _ (cp_conjAut_relation E ρ hρ))).Vs ⊓
          (abelianWeightOneHodgeStructure (E ⊗ E)).H (1, 0)) = 2 := by
    rw [hdim] at h2; exact h2
  have hw : 2 * Module.finrank ℂ ↥((cp_weilAction (E ⊗ E) (cp_conjAut E ρ)
        (cp_weilOperator_sq _ _ (cp_conjAut_relation E ρ hρ))).Vs ⊓
          (abelianWeightOneHodgeStructure (E ⊗ E)).H (1, 0)) =
      Module.finrank ℂ ↥(cp_weilAction (E ⊗ E) (cp_conjAut E ρ)
        (cp_weilOperator_sq _ _ (cp_conjAut_relation E ρ hρ))).Vs := hW
  refine ⟨by rw [hdim]; norm_num, by omega, ?_⟩
  exact HodgeBlocks.finrank_range_exteriorPower_map_subtype_of_finrank ℂ _ _ 2 (by omega)

/-- Instance check: a curve satisfying every hypothesis exists (C3 on `main`). -/
example : ∃ (E : Over (Spec ↧ℂ)) (_ : GrpObj E) (_ : IsCommMonObj E) (_ : IsIntegral E.left)
    (ρ : E ⟶ E), Smooth E.hom ∧ IsProjective E.hom ∧ TopologicalSpace.dim E.left = 1 ∧
      IsMonHom ρ ∧ 𝟙 E * ρ * (ρ ≫ ρ) = 1 ∧ ρ ≠ 𝟙 E := by
  obtain ⟨E, G, hI, ρ, hS, hP, hd, hM, hρ, e, -, he⟩ := cp_exists_cm_curve
  have hc : IsCommMonObj E :=
    isCommMonObj_of_complexSelfProductIntegral E (complexSelfProductIntegral_of_isIntegral E)
  refine ⟨E, G, hc, hI, ρ, hS, hP, hd, hM, hρ, fun h => ?_⟩
  obtain ⟨P, hP⟩ := e.surjective (.some 2 3 cp_W_nonsingular_two_three)
  have := he P
  rw [h, Category.comp_id, hP] at this
  have h' : cp_cubicAut (.some 2 3 cp_W_nonsingular_two_three) =
      .some (cp_zeta * 2) 3 _ := rfl
  rw [h', WeierstrassCurve.Affine.Point.some.injEq] at this
  have hz : cp_zeta = 1 := by linear_combination -this.1 / 2
  have := cp_zeta_sq_add
  rw [hz] at this
  norm_num at this

/-- Arithmetic check: `(1 + ζ)² = ζ`, it differs from its conjugate and from `1`, and the two
eigenvalues feed `g34c_two_independent`. -/
example : (1 + cp_zeta) ^ 2 = cp_zeta ∧ (1 + cp_zeta) ^ 2 ≠ conj ((1 + cp_zeta) ^ 2) ∧
    (1 + cp_zeta) ^ 2 ≠ 1 := by
  have hz := cp_zeta_sq_add
  have hsq : (1 + cp_zeta) ^ 2 = cp_zeta := by linear_combination hz
  have him : cp_zeta.im ≠ 0 := by
    simp only [cp_zeta, Complex.div_ofNat_im, Complex.add_im, Complex.neg_im, Complex.one_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
    have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    intro h
    linarith
  refine ⟨hsq, ?_, ?_⟩
  · rw [hsq]
    intro h
    apply him
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  · rw [hsq]
    intro h
    apply him
    rw [h, Complex.one_im]

example (c : ℂ) (hc : c ≠ 0) :
    !![c, conj c;
      c * conj ((1 : ℂ) + cp_zeta) ^ 2, conj (c * conj ((1 : ℂ) + cp_zeta) ^ 2)].det ≠ 0 :=
  g34c_two_independent cp_zeta c cp_zeta_sq_add hc

end Surface

/-! ### Scalar extension of the normalization and of the vanishing -/

section ScalarExtension

variable (A Y : Over (Spec ↧ℂ))
  [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- **Scalar extension of the normalization.** If `P (a × b) = I(b) a` on rational classes in
bidegree `(6, 4)`, then `P_ℂ (a × b) = I_ℂ(b) a` for complex classes: both sides are
`ℂ`-bilinear and agree on pure tensors.
Source: Bourbaki, *Algebra*, Chapter II, §5 (extension of scalars); Hatcher, *Algebraic
Topology*, §3.2; the C7 normalization of `docs/specs/CompensationAssembly.md`. -/
theorem cq8_crossC_normalization (I : HQ Y 4 →ₗ[ℚ] ℚ) (P : HQ (A ⊗ Y) 10 →ₗ[ℚ] HQ A 6)
    (h : ∀ (a : HQ A 6) (b : HQ Y 4), P (cq8_cross A Y 6 4 a b) = I b • a)
    (a : ℂ ⊗[ℚ] HQ A 6) (b : ℂ ⊗[ℚ] HQ Y 4) :
    P.baseChange ℂ (cq8_crossC A Y 6 4 a b) = cq8_scalarC I b • a :=
  cq8_crossC_normalization_aux A Y I P h a b

/-- The tensor model `P = rid ∘ (id ⊗ I)` is not a zero map: on `H⁶ ⊗ H⁴` with a nonzero `a` and
`b = I⁻¹ 1` it returns `a`. So the normalization hypothesis does not force `P = 0`. -/
example (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (a : HQ A 6) (ha : a ≠ 0) :
    (TensorProduct.rid ℚ (HQ A 6)) (TensorProduct.map LinearMap.id I.toLinearMap
      (a ⊗ₜ[ℚ] I.symm 1)) ≠ 0 := by
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, TensorProduct.rid_tmul, one_smul] using ha

/-- **Scalar extension of the vanishing.** If `P` kills every rational cross product in
bidegree `(i, j)`, it kills every complex one: `P_ℂ` and the complex cross product are base
changes, and pure tensors span.
Source: Bourbaki, *Algebra*, Chapter II, §5 (extension of scalars); the C7 vanishing of
`docs/specs/CompensationAssembly.md`. -/
theorem cq8_crossC_vanishing {U : Type*} [AddCommGroup U] [Module ℚ U] {n : ℕ}
    (i j : ℕ) (hij : i + j = n) (P : HQ (A ⊗ Y) n →ₗ[ℚ] U)
    (h : ∀ (a : HQ A i) (b : HQ Y j),
      P (HQ.castEquiv (A ⊗ Y) hij (cq8_cross A Y i j a b)) = 0)
    (a : ℂ ⊗[ℚ] HQ A i) (b : ℂ ⊗[ℚ] HQ Y j) :
    P.baseChange ℂ ((HQ.castEquiv (A ⊗ Y) hij).toLinearMap.baseChange ℂ
      (cq8_crossC A Y i j a b)) = 0 :=
  cq8_crossC_vanishing_aux A Y i j hij P h a b

example := @cq8_crossC_vanishing

/-- The complex cross product is not zero: the cross product of the two units, complexified,
is nonzero. -/
example : cq8_crossC A Y 0 0 (1 ⊗ₜ cupUnit A) (1 ⊗ₜ cupUnit Y) ≠ 0 := by
  have hr : cq8_crossC A Y 0 0 (1 ⊗ₜ cupUnit A) (1 ⊗ₜ cupUnit Y) =
      HodgeBlocks.complexify _ (cq8_cross A Y 0 0 (cupUnit A) (cupUnit Y)) := by
    simp only [cq8_crossC, cq8_cross, LinearMap.compl₁₂_apply, LinearMap.baseChange_tmul,
      CupProduct.cupC_tmul, mul_one]
    rfl
  have hq : cq8_cross A Y 0 0 (cupUnit A) (cupUnit Y) ≠ 0 := by
    simp only [cq8_cross, LinearMap.compl₁₂_apply]
    rw [spec_homPullback_unit, spec_homPullback_unit]
    have cq8_h := cupProductOf_constants (A ⊗ Y) 1 1
    simp only [one_smul, mul_one] at cq8_h
    rw [cq8_h]
    exact cupProductOf_unit_ne_zero (A ⊗ Y)
  rw [hr]
  intro h
  exact hq (HodgeBlocks.complexify_injective (h.trans (map_zero _).symm))

end ScalarExtension

end HodgeLean.Foundations.Program

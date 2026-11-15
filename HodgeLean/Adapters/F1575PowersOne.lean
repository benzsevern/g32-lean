import HodgeLean.Adapters.F1575PowersOneDefs

/-! # Multiplicity-one transport lemmas for F-1575 powers -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry ComplexPoint
open scoped TensorProduct

namespace HodgeLean.Adapters
open RealDefs Foundations Foundations.WeilPower InvariantsExterior

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μ : CupProduct X} [GrpObj X]
  {hF : FiniteBetti X} {hB : BettiDeRhamIso X} {hD : HodgeDecomposition X}
  {hT : TorusCohomology μ}
  {A : letI := hT.finite
    HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3}
  {η : HQ X 2}

/-- The chosen flattening at multiplicity one is the canonical single-copy equivalence. -/
theorem powerOneFlatten_eq_f1575SingleCopy (X : Over (Spec ↧ℂ)) :
    powerOneFlatten X = (f1575SingleCopy (V := HQ X 1)).toLinearMap := by
  ext x c
  simp [powerOneFlatten, f1575SingleCopy]

/-- Exterior powers of a linear map preserve wedge products. -/
theorem exteriorPower_map_wedge {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] (f : U →ₗ[ℚ] V) (i j : ℕ)
    (u : ⋀[ℚ]^i U) (v : ⋀[ℚ]^j U) :
    exteriorPower.map (i + j) f (exteriorPower.wedge ℚ U i j u v) =
      exteriorPower.wedge ℚ V i j (exteriorPower.map i f u) (exteriorPower.map j f v) := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map, Symplectic.coe_wedge]
  exact map_mul (ExteriorAlgebra.map f) u.val v.val

/-- At multiplicity one, C7 after flattening is the established single-copy map. -/
theorem powerOne_cupWedge_map_eq_f1575SingleCopyCohomologyQ (k : ℕ) :
    (hT.cupWedgeEquiv k).toLinearMap ∘ₗ exteriorPower.map k (powerOneFlatten X) =
      f1575SingleCopyCohomologyQ μ k := by
  rw [powerOneFlatten_eq_f1575SingleCopy]
  rfl

/-- At multiplicity one, a Weil pullback becomes the expected `r + sJ` map
after flattening. -/
theorem powerOneFlatten_comp_weilPowerPullback (J : Module.End ℚ (HQ X 1))
    (r s : Fin 1 → ℚ) :
    powerOneFlatten X ∘ₗ weilPowerPullback J r s =
      r 0 • LinearMap.id + s 0 • J := by
  ext x
  simp [powerOneFlatten, weilPowerPullback]

/-- An affine polynomial in an operator preserves every exterior power of one
of the operator's eigenspaces. -/
theorem exterior_map_linear_preserves_eigenspace_range {V : Type*} [AddCommGroup V]
    [Module ℂ V] (T : Module.End ℂ V) (c a b : ℂ) (n : ℕ) :
    (LinearMap.range (exteriorPower.map n (Module.End.eigenspace T c).subtype)).map
      (exteriorPower.map n (a • LinearMap.id + b • T)) ≤
      LinearMap.range (exteriorPower.map n (Module.End.eigenspace T c).subtype) := by
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with ⟨y, rfl⟩
  refine ⟨exteriorPower.map n ((a + b * c) • LinearMap.id) y, ?_⟩
  have hbase : (Module.End.eigenspace T c).subtype.comp ((a + b * c) • LinearMap.id) =
      (a • LinearMap.id + b • T).comp (Module.End.eigenspace T c).subtype := by
    ext z
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
    change (a + b * c) • (z : V) = a • (z : V) + b • T z
    rw [Module.End.mem_eigenspace_iff.mp z.property]
    module
  have hext := congrArg (exteriorPower.map n) hbase
  simpa only [exteriorPower.map_comp, LinearMap.comp_apply] using
    DFunLike.congr_fun hext y

private theorem baseChange_affine {V : Type*} [AddCommGroup V] [Module ℚ V]
    (J : Module.End ℚ V) (r s : ℚ) :
    (r • LinearMap.id + s • J).baseChange ℂ =
      (r : ℂ) • LinearMap.id + (s : ℂ) • J.baseChange ℂ := by
  rw [LinearMap.baseChange_add, LinearMap.baseChange_smul, LinearMap.baseChange_smul,
    LinearMap.baseChange_id]
  rfl

set_option maxHeartbeats 400000 in
/-- Rational Weil classes are stable under every affine rational polynomial in the Weil
operator. -/
theorem weilClasses_map_linear_mem (hM : IsMemberOfM hF hB hD hT A η) (r s : ℚ) :
    letI := hT.finite
    let W := A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType
    ∀ w ∈ W, exteriorPower.map _ (r • LinearMap.id + s • A.J) w ∈ W := by
  letI := hT.finite
  dsimp only
  intro w hw
  change HodgeBlocks.complexifyWedge _ (exteriorPower.map _ (r • LinearMap.id + s • A.J) w) ∈
    ((LinearMap.range (exteriorPower.map _ A.Vs.subtype) ⊔
      LinearMap.range (exteriorPower.map _ A.Vsbar.subtype)).restrictScalars ℚ)
  rw [HodgeBlocks.complexifyWedge_exteriorPower_map, baseChange_affine]
  let n := Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) +
    Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0))
  let R : Submodule ℂ (⋀[ℂ]^n (ℂ ⊗[ℚ] HQ X 1)) :=
    LinearMap.range (exteriorPower.map n A.Vs.subtype) ⊔
      LinearMap.range (exteriorPower.map n A.Vsbar.subtype)
  have hVs := exterior_map_linear_preserves_eigenspace_range A.Jc
    (HodgeBlocks.WeilAction.omegaC 3) (r : ℂ) (s : ℂ) n
  have hVsbar := exterior_map_linear_preserves_eigenspace_range A.Jc
    (-HodgeBlocks.WeilAction.omegaC 3) (r : ℂ) (s : ℂ) n
  have hmap : R.map (exteriorPower.map n ((r : ℂ) • LinearMap.id + (s : ℂ) • A.Jc)) ≤ R := by
    dsimp only [R]
    rw [Submodule.map_sup]
    exact sup_le_sup hVs hVsbar
  exact hmap ⟨_, hw, rfl⟩

/-- Extend an even-degree rational cohomology family by zero in odd degrees.
Source: driver construction for the comparison family in the S1 closure argument
(`docs/briefs/f1575-powers-fix.md`, driver hints); every generator there has even degree. -/
def f1575EvenCohomologySpanQ (D : ∀ p : ℕ, Submodule ℚ (HQ X (2 * p))) (k : ℕ) :
    Submodule ℚ (HQ X k) where
  carrier := {v | v = 0 ∨ ∃ (p : ℕ) (h : k = 2 * p), HQ.castEquiv X h v ∈ D p}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro v w hv hw
    rcases hv with rfl | ⟨p, rfl, hv⟩
    · simpa only [zero_add] using hw
    rcases hw with rfl | ⟨q, hq, hw⟩
    · exact Or.inr ⟨p, rfl, by simpa only [add_zero] using hv⟩
    have hpq : q = p := by omega
    subst q
    exact Or.inr ⟨p, rfl, (D p).add_mem hv hw⟩
  smul_mem' := by
    intro c v hv
    rcases hv with rfl | ⟨p, rfl, hv⟩
    · exact Or.inl (smul_zero c)
    exact Or.inr ⟨p, rfl, (D p).smul_mem c hv⟩

theorem f1575EvenCohomologySpanQ_even (D : ∀ p : ℕ, Submodule ℚ (HQ X (2 * p)))
    (p : ℕ) : f1575EvenCohomologySpanQ D (2 * p) = D p := by
  ext v
  constructor
  · rintro (rfl | ⟨q, hq, hv⟩)
    · exact Submodule.zero_mem _
    obtain rfl : q = p := by omega
    exact hv
  · exact fun hv => Or.inr ⟨p, rfl, hv⟩

example (D : ∀ p : ℕ, Submodule ℚ (HQ X (2 * p))) (p : ℕ) :
    f1575EvenCohomologySpanQ D (2 * p) = D p :=
  f1575EvenCohomologySpanQ_even D p

theorem f1575EvenCohomologySpanQ_cup
    (D : ∀ p : ℕ, Submodule ℚ (HQ X (2 * p)))
    (hc : ∀ {p q : ℕ} (h : 2 * p + 2 * q = 2 * (p + q)) (a : HQ X (2 * p))
      (b : HQ X (2 * q)), a ∈ D p → b ∈ D q → μ.cup h a b ∈ D (p + q))
    {i j k : ℕ} (h : i + j = k) {a : HQ X i} {b : HQ X j}
    (ha : a ∈ f1575EvenCohomologySpanQ D i) (hb : b ∈ f1575EvenCohomologySpanQ D j) :
    μ.cup h a b ∈ f1575EvenCohomologySpanQ D k := by
  rcases ha with rfl | ⟨p, rfl, ha⟩
  · rw [map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  rcases hb with rfl | ⟨q, rfl, hb⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  refine Or.inr ⟨p + q, by omega, ?_⟩
  rw [CupProduct.castEquiv_cup]
  exact hc (by omega) _ _ ha hb


/-- The degree-two rational exterior Hodge space transports to geometric divisors at `m = 1`. -/
theorem powerOne_rationalExteriorHodge_map_eq (hC : CupFiltered X μ) (p : ℕ) :
    letI := hT.finite
    (rationalExteriorHodge (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
      (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal 1 (2 * p)).map
      ((hT.cupWedgeEquiv (2 * p)).toLinearMap ∘ₗ
        exteriorPower.map (2 * p) (powerOneFlatten X)) = Hdg^p(X; ℚ) := by
  letI := hT.finite
  rw [powerOne_cupWedge_map_eq_f1575SingleCopyCohomologyQ]
  exact f1575_rationalHodge_map_eq hF hB hD hT hC p

end HodgeLean.Adapters

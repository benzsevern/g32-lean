import HodgeLean.RealDefs.WeilClasses
import HodgeLean.Foundations.WeilPowerClasses
import HodgeLean.Adapters.F1575Exterior
import HodgeLean.Foundations.Symplectic

/-! # Products in the complexification of the divisor-Weil span -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint
open scoped TensorProduct

namespace HodgeLean.Adapters
open RealDefs Foundations Foundations.WeilPower

set_option maxHeartbeats 1600000

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μ : CupProduct X}

/-- A rational cup-closed family remains cup-closed after scalar extension. -/
theorem f1575_cupC_mem_baseChange {i j k : ℕ} (h : i + j = k)
    (P : Submodule ℚ (HQ X i)) (Q : Submodule ℚ (HQ X j)) (R : Submodule ℚ (HQ X k))
    (hmul : ∀ a ∈ P, ∀ b ∈ Q, μ.cup h a b ∈ R)
    {a : ℂ ⊗[ℚ] HQ X i} {b : ℂ ⊗[ℚ] HQ X j}
    (ha : a ∈ P.baseChange ℂ) (hb : b ∈ Q.baseChange ℂ) :
    μ.cupC h a b ∈ R.baseChange ℂ := by
  rw [Submodule.baseChange_eq_span] at ha hb
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, ha, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b, hb, rfl⟩ := hb
      rw [TensorProduct.mk_apply, TensorProduct.mk_apply, CupProduct.cupC_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem _ (hmul a ha b hb)
    | zero => simp
    | add b c _ _ hb hc => simpa only [map_add] using (R.baseChange ℂ).add_mem hb hc
    | smul c b _ hb => simpa only [map_smul] using (R.baseChange ℂ).smul_mem c hb
  | zero => simp
  | add a c _ _ ha hc =>
    simpa only [map_add, LinearMap.add_apply] using (R.baseChange ℂ).add_mem ha hc
  | smul c a _ ha =>
    simpa only [map_smul, LinearMap.smul_apply] using (R.baseChange ℂ).smul_mem c ha

theorem f1575_castC_self (k : ℕ) (h : k = k) (v : ℂ ⊗[ℚ] HQ X k) :
    (HQ.castEquiv X h).toLinearMap.baseChange ℂ v = v := by
  induction v using TensorProduct.inductionOn with
  | tmul a v => simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, HQ.castEquiv_apply_self]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem f1575_castC_cupC {i j k l : ℕ} (h : i + j = k) (h' : k = l)
    (a : ℂ ⊗[ℚ] HQ X i) (b : ℂ ⊗[ℚ] HQ X j) :
    (HQ.castEquiv X h').toLinearMap.baseChange ℂ (μ.cupC h a b) =
      μ.cupC (h.trans h') a b := by
  induction a using TensorProduct.inductionOn with
  | tmul z a =>
    induction b using TensorProduct.inductionOn with
    | tmul w b => simp only [CupProduct.cupC_tmul, LinearMap.baseChange_tmul,
        LinearEquiv.coe_coe, CupProduct.castEquiv_cup]
    | add b c hb hc => simp only [map_add, hb, hc]
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]

/-- Extend an even-degree rational family to every degree, putting zero in odd degrees.

Source: constructed here for F-1575 step 3 to package the divisor-Weil family
as a graded complex submodule. -/
def f1575EvenCohomologySpan (D : ∀ p : ℕ, Submodule ℚ (HQ X (2 * p))) (k : ℕ) :
    Submodule ℂ (ℂ ⊗[ℚ] HQ X k) where
  carrier := {v | v = 0 ∨ ∃ (p : ℕ) (h : k = 2 * p),
    (HQ.castEquiv X h).toLinearMap.baseChange ℂ v ∈ (D p).baseChange ℂ}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro v w hv hw
    rcases hv with rfl | ⟨p, rfl, hv⟩
    · simpa only [zero_add] using hw
    rcases hw with rfl | ⟨q, hq, hw⟩
    · rw [add_zero]; exact Or.inr ⟨p, rfl, hv⟩
    have hpq : q = p := by omega
    subst q
    rw [f1575_castC_self] at hv hw
    exact Or.inr ⟨p, rfl, by rw [f1575_castC_self]; exact (D p).baseChange ℂ |>.add_mem hv hw⟩
  smul_mem' := by
    intro c v hv
    rcases hv with rfl | ⟨p, rfl, hv⟩
    · simp only [smul_zero]; exact Or.inl rfl
    refine Or.inr ⟨p, rfl, ?_⟩
    rw [map_smul]
    exact ((D p).baseChange ℂ).smul_mem c hv

example (D : ∀ p : ℕ, Submodule ℚ (HQ X (2 * p))) (k : ℕ) :
    Submodule ℂ (ℂ ⊗[ℚ] HQ X k) :=
  f1575EvenCohomologySpan D k

theorem f1575EvenCohomologySpan_even (D : ∀ p : ℕ, Submodule ℚ (HQ X (2 * p))) (p : ℕ) :
    f1575EvenCohomologySpan D (2 * p) = (D p).baseChange ℂ := by
  ext v
  constructor
  · rintro (rfl | ⟨q, hq, hv⟩)
    · exact Submodule.zero_mem _
    obtain rfl : q = p := by omega
    simpa only [f1575_castC_self] using hv
  · exact fun hv => Or.inr ⟨p, rfl, by simpa only [f1575_castC_self] using hv⟩

/-- Cup closure for the extension of an even-degree cup-closed family. -/
theorem f1575EvenCohomologySpan_cup (D : ∀ p : ℕ, Submodule ℚ (HQ X (2 * p)))
    (hc : ∀ {p q : ℕ} (h : 2 * p + 2 * q = 2 * (p + q)) (a : HQ X (2 * p))
      (b : HQ X (2 * q)), a ∈ D p → b ∈ D q → μ.cup h a b ∈ D (p + q))
    {i j k : ℕ} (h : i + j = k) {a : ℂ ⊗[ℚ] HQ X i} {b : ℂ ⊗[ℚ] HQ X j}
    (ha : a ∈ f1575EvenCohomologySpan D i) (hb : b ∈ f1575EvenCohomologySpan D j) :
    μ.cupC h a b ∈ f1575EvenCohomologySpan D k := by
  rcases ha with rfl | ⟨p, rfl, ha⟩
  · rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  rcases hb with rfl | ⟨q, rfl, hb⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  rw [f1575_castC_self] at ha hb
  refine Or.inr ⟨p + q, by omega, ?_⟩
  rw [f1575_castC_cupC]
  exact f1575_cupC_mem_baseChange _ (D p) (D q) (D (p + q))
    (fun a ha b hb => hc _ a b ha hb) ha hb

section Exterior

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Reindex an exterior degree along an equality, without changing the vector.

Source: constructed here for F-1575 step 3 as transport along equality of
exterior degrees. -/
def f1575ExteriorCast {i j : ℕ} (h : i = j) : (⋀[ℂ]^i V) ≃ₗ[ℂ] (⋀[ℂ]^j V) :=
  h ▸ LinearEquiv.refl ℂ (⋀[ℂ]^i V)

example (i : ℕ) : (⋀[ℂ]^i V) ≃ₗ[ℂ] (⋀[ℂ]^i V) := f1575ExteriorCast rfl

theorem f1575ExteriorCast_range {i j : ℕ} (h : i = j) (P : Submodule ℂ V)
    {v : ⋀[ℂ]^i V} (hv : v ∈ LinearMap.range (exteriorPower.map i P.subtype)) :
    f1575ExteriorCast h v ∈ LinearMap.range (exteriorPower.map j P.subtype) := by
  subst j
  exact hv

/-- Exterior functoriality respects products. -/
theorem f1575_exterior_map_wedge (f : V →ₗ[ℂ] W) (i j : ℕ)
    (v : ⋀[ℂ]^i V) (w : ⋀[ℂ]^j V) :
    exteriorPower.map (i + j) f (exteriorPower.wedge ℂ V i j v w) =
      exteriorPower.wedge ℂ W i j (exteriorPower.map i f v) (exteriorPower.map j f w) := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map, Symplectic.coe_wedge]
  exact map_mul (ExteriorAlgebra.map f) v.val w.val

/-- The inverse exterior equivalence is the exterior map of the inverse. -/
theorem f1575_exteriorEquiv_symm (e : V ≃ₗ[ℂ] W) (k : ℕ) (v : ⋀[ℂ]^k W) :
    (exteriorEquiv k e).symm v = exteriorPower.map k e.symm.toLinearMap v := by
  apply (exteriorEquiv k e).injective
  rw [LinearEquiv.apply_symm_apply]
  change v = exteriorPower.map k e.toLinearMap (exteriorPower.map k e.symm.toLinearMap v)
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  simp

end Exterior

section RationalExterior

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

theorem f1575_singleCopyModel_symm_pure {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (z : W × Module.Dual ℂ W) (u : Fin 1 → ℂ) :
    f1575SingleCopyComplex ((powerModel 1 e).symm
      (TensorProduct.prodLeft ℂ ℂ W (Module.Dual ℂ W) (Fin 1 → ℂ) (z ⊗ₜ[ℂ] u))) =
      u 0 • e.symm z := by
  simp [powerModel, f1575SingleCopyComplex, LinearEquiv.funUnique]

theorem f1575_singleCopyModel_symm_vector {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (x : W) (u : Fin 1 → ℂ) :
    f1575SingleCopyComplex ((powerModel 1 e).symm (InvariantsExterior.vectorIn u x)) =
      u 0 • e.symm (x, 0) := by
  simpa only [TensorProduct.prodLeft_tmul, TensorProduct.zero_tmul,
    InvariantsExterior.vectorIn_apply] using f1575_singleCopyModel_symm_pure e (x, 0) u

theorem f1575_singleCopyModel_symm_dual {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (x : Module.Dual ℂ W) (u : Fin 1 → ℂ) :
    f1575SingleCopyComplex ((powerModel 1 e).symm (InvariantsExterior.dualIn u x)) =
      u 0 • e.symm (0, x) := by
  simpa only [TensorProduct.prodLeft_tmul, TensorProduct.zero_tmul,
    InvariantsExterior.dualIn_apply] using f1575_singleCopyModel_symm_pure e (0, x) u

/-- Complexification of rational wedges is multiplicative. -/
theorem f1575_complexifyWedge_wedge (i j : ℕ) (v : ⋀[ℚ]^i V) (w : ⋀[ℚ]^j V) :
    HodgeBlocks.complexifyWedge (i + j) (exteriorPower.wedge ℚ V i j v w) =
      exteriorPower.wedge ℂ (ℂ ⊗[ℚ] V) i j
        (HodgeBlocks.complexifyWedge i v) (HodgeBlocks.complexifyWedge j w) := by
  have hh : (exteriorPower.wedge ℚ V i j).compr₂ (HodgeBlocks.complexifyWedge (i + j)) =
      ((LinearMap.restrictScalarsₗ (R := ℚ) (R₁ := ℚ) (S := ℂ)
        (M := ⋀[ℂ]^j (ℂ ⊗[ℚ] V)) (N := ⋀[ℂ]^(i + j) (ℂ ⊗[ℚ] V))).comp
        ((exteriorPower.wedge ℂ (ℂ ⊗[ℚ] V) i j).restrictScalars ℚ)).compl₁₂
          (HodgeBlocks.complexifyWedge i) (HodgeBlocks.complexifyWedge j) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro b
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compr₂_apply,
      LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.restrictScalarsₗ_apply, InvariantsExterior.wedge_ιMulti,
      HodgeBlocks.complexifyWedge_ιMulti]
    congr 1
    funext s
    refine Fin.addCases (fun s => ?_) (fun s => ?_) s <;> simp
  exact LinearMap.congr_fun₂ hh v w

end RationalExterior

variable [GrpObj X]

/-- The complexified cup-wedge equivalence with complex exterior source.

Source: constructed here for F-1575 step 3 from C7 (`TorusCohomology`) and
the standard exterior base-change equivalence. -/
def f1575ExteriorCohomology (hT : TorusCohomology μ) (k : ℕ) :
    letI := hT.finite
    (⋀[ℂ]^k (ℂ ⊗[ℚ] HQ X 1)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ X k) :=
  letI := hT.finite
  letI := (finiteBetti_of_torusCohomology hT).finite k
  (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv k).symm.trans
    (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^k (HQ X 1))
      (W := HQ X k) (hT.cupWedgeEquiv k))

example (hT : TorusCohomology μ) (k : ℕ) :
    letI := hT.finite
    (⋀[ℂ]^k (ℂ ⊗[ℚ] HQ X 1)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ X k) :=
  f1575ExteriorCohomology hT k

theorem f1575ExteriorCohomology_eq_baseChange (hT : TorusCohomology μ) (k : ℕ)
    (v : ⋀[ℂ]^k (ℂ ⊗[ℚ] HQ X 1)) :
    letI := hT.finite
    f1575ExteriorCohomology hT k v = (μ.cupWedgeMap k).baseChange ℂ
      ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv k).symm v) := by
  let := hT.finite
  let := (finiteBetti_of_torusCohomology hT).finite k
  unfold f1575ExteriorCohomology
  rw [LinearEquiv.trans_apply]
  generalize (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv k).symm v = z
  induction z using TensorProduct.inductionOn with
  | tmul a v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem f1575_castC_exteriorCohomology (hT : TorusCohomology μ) {i j : ℕ} (h : i = j)
    (v : ⋀[ℂ]^i (ℂ ⊗[ℚ] HQ X 1)) :
    letI := hT.finite
    (HQ.castEquiv X h).toLinearMap.baseChange ℂ (f1575ExteriorCohomology hT i v) =
      f1575ExteriorCohomology hT j (f1575ExteriorCast h v) := by
  let := hT.finite
  subst j
  rw [f1575_castC_self]
  rfl

theorem f1575ExteriorCohomology_complexify (hT : TorusCohomology μ) (k : ℕ)
    (v : ⋀[ℚ]^k (HQ X 1)) :
    letI := hT.finite
    f1575ExteriorCohomology hT k (HodgeBlocks.complexifyWedge k v) =
      (1 : ℂ) ⊗ₜ[ℚ] μ.cupWedgeMap k v := by
  let := hT.finite
  let := (finiteBetti_of_torusCohomology hT).finite k
  rw [← HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul]
  simp only [f1575ExteriorCohomology, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, HodgeBlocks.QHodgeStructure.complexificationCongr_tmul,
    TorusCohomology.cupWedgeEquiv_apply]

/-- The complexified torus map respects exterior multiplication in all degrees. -/
theorem f1575ExteriorCohomology_wedge (hT : TorusCohomology μ) (i j : ℕ)
    (v : ⋀[ℂ]^i (ℂ ⊗[ℚ] HQ X 1)) (w : ⋀[ℂ]^j (ℂ ⊗[ℚ] HQ X 1)) :
    letI := hT.finite
    f1575ExteriorCohomology hT (i + j) (exteriorPower.wedge ℂ _ i j v w) =
      μ.cupC rfl (f1575ExteriorCohomology hT i v) (f1575ExteriorCohomology hT j w) := by
  let := hT.finite
  let B (k : ℕ) := (Module.finBasis ℚ (HQ X 1)).exteriorPower k
  let BC (k : ℕ) := ((B k).baseChange ℂ).map
    (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := HQ X 1) k)
  have hh : (exteriorPower.wedge ℂ (ℂ ⊗[ℚ] HQ X 1) i j).compr₂
      (f1575ExteriorCohomology hT (i + j)).toLinearMap =
      (μ.cupC rfl).compl₁₂ (f1575ExteriorCohomology hT i).toLinearMap
        (f1575ExteriorCohomology hT j).toLinearMap := by
    apply (BC i).ext
    intro s
    apply (BC j).ext
    intro t
    change f1575ExteriorCohomology hT (i + j)
      (exteriorPower.wedge ℂ _ i j (BC i s) (BC j t)) =
        μ.cupC rfl (f1575ExteriorCohomology hT i (BC i s))
          (f1575ExteriorCohomology hT j (BC j t))
    simp only [BC, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul]
    rw [← f1575_complexifyWedge_wedge, f1575ExteriorCohomology_complexify,
      f1575ExteriorCohomology_complexify, f1575ExteriorCohomology_complexify,
      CupProduct.cupC_tmul, one_mul, CupProduct.cupWedgeMap_wedge]
  exact LinearMap.congr_fun₂ hh v w

end HodgeLean.Adapters

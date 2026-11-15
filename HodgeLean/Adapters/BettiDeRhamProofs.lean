import HodgeLean.Adapters.TorusCohomologyChecks
import HodgeLean.RealDefs.FundamentalClassUnit
import HodgeLean.Foundations.Connected

/-! # Proofs for the Betti–de Rham specification

* Injectivity: a `ℚ`-linear `π : ℂ → ℚ` induces `ℂ[0] → ℚ[0]`, and with the inverse of the
  Poincaré comparison `complexConstantCohomologyDeRhamAddEquiv` it gives `deRhamReadBack`,
  `H_dR^n(X) → H^n(X; ℚ)`. Since `constantsToHolomorphicDeRhamComplexInt` intertwines the complex
  scalars, `deRhamReadBack π ∘ bettiDeRhamHQ` is `π ⊗ id`. Taking `π` to run over the coordinate
  functionals of a `ℚ`-basis of `ℂ` recovers every component of `ℂ ⊗[ℚ] HQ X n ≃ (ι →₀ HQ X n)`.
* The finrank criterion: injectivity with `Module.finrank_baseChange`; the abelian assembly adds
  `finiteBetti_abelian` and `finrank_HQ_abelian`.
* The unit: reading `1 ⊗ [X]` back through a coordinate functional nonzero at `1` gives a nonzero
  multiple of `unitClass X`, which is nonzero by `unitClass_ne_zero'`.
* Degree zero: `X(ℂ)` is path connected, so every global section of the constant sheaf `ℂ` is
  constant (`exists_eq_constSection`), and `H^0(X; ℂ) ≃ H_dR^0(X)` carries `c` times the image of
  the constant rational section `1` to `c` times its de Rham class. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

section ReadBack

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The map `ℂ[0] → ℚ[0]` of constant complexes induced by a `ℚ`-linear `π : ℂ → ℚ`. -/
def complexToRatConstantComplex (π : ℂ →ₗ[ℚ] ℚ) :
    constantComplexSheafComplexInt X ⟶ constantFieldSheafComplexInt ℚ X :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
        (AddCommGrpCat.ofHom π.toAddMonoidHom))) ComplexShape.embeddingUpNat

/-- Reading a de Rham class back to rational cohomology through `π : ℂ → ℚ`. -/
def deRhamReadBack (π : ℂ →ₗ[ℚ] ℚ) (n : ℕ) : H_dR^(n : ℤ)(X) →+ H^n(X; ℚ) :=
  (hypercohomologyAddEquivConstantCohomology ℚ X n).toAddMonoidHom.comp
    ((hypercohomologyMap X (complexToRatConstantComplex X π) n).comp
      (complexConstantCohomologyDeRhamAddEquiv X n).symm.toAddMonoidHom)

omit [IsIntegral X.left] [Smooth X.hom] in
lemma ratToComplex_scalar_complexToRat (π : ℂ →ₗ[ℚ] ℚ) (z : ℂ) :
    fieldToComplexConstantSheafComplexInt ℚ X ≫ complexScalarComplexInt X z ≫
      complexToRatConstantComplex X π = fieldScalarComplex ℚ X (π z) := by
  have hs : fieldToComplexConstantSheaf ℚ X ≫ complexScalarSheaf X z ≫
      (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
        (AddCommGrpCat.ofHom π.toAddMonoidHom) = fieldScalarSheaf ℚ X (π z) := by
    change (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
        (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom) ≫
          (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
            (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ z)) ≫
          (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
            (AddCommGrpCat.ofHom π.toAddMonoidHom) =
      (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
        (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (π z)))
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext q
    change π (z * algebraMap ℚ ℂ q) = π z * q
    rw [mul_comm z, ← Algebra.smul_def, π.map_smul, smul_eq_mul, mul_comm]
  rw [fieldToComplexConstantSheafComplexInt, complexScalarComplexInt, complexToRatConstantComplex,
    fieldScalarComplex, ← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  change HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map (fieldToComplexConstantSheaf ℚ X) ≫
        (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map (complexScalarSheaf X z) ≫
          (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
            ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
              (AddCommGrpCat.ofHom π.toAddMonoidHom))) _ = _
  rw [← hs, (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map_comp]
  congr 2
  exact ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map_comp _ _).symm

lemma deRhamReadBack_smul_fieldToDeRham (π : ℂ →ₗ[ℚ] ℚ) (n : ℕ) (z : ℂ) (v : H^n(X; ℚ)) :
    deRhamReadBack X π n (z • fieldToDeRhamCohomology ℚ X n v) = π z • v := by
  rw [deRham_complex_smul_eq]
  unfold fieldToDeRhamCohomology fieldToHolomorphicDeRhamComplexInt
  simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
  rw [← hypercohomologyMap_comp_apply, Category.assoc, constantsToHolomorphicDeRhamComplexInt_scalar,
    ← Category.assoc, hypercohomologyMap_comp_apply]
  change hypercohomologyAddEquivConstantCohomology ℚ X n
      (hypercohomologyMap X (complexToRatConstantComplex X π) n
        ((complexConstantCohomologyDeRhamAddEquiv X n).symm
          (complexConstantCohomologyDeRhamAddEquiv X n _))) = _
  rw [AddEquiv.symm_apply_apply, ← hypercohomologyMap_comp_apply, Category.assoc,
    ratToComplex_scalar_complexToRat, ← hypercohomologyAddEquivConstantCohomology_symm_smul,
    AddEquiv.apply_symm_apply]


/-- Reading back `bettiDeRhamHQ` through `π` is `π ⊗ id`. -/
lemma deRhamReadBack_bettiDeRhamHQ (π : ℂ →ₗ[ℚ] ℚ) (n : ℕ) (x : ℂ ⊗[ℚ] HQ X n) :
    deRhamReadBack X π n (bettiDeRhamHQ X n x) =
      TensorProduct.lid ℚ (HQ X n) (LinearMap.rTensor (HQ X n) π x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z v =>
    rw [bettiDeRhamHQ_tmul]
    refine (deRhamReadBack_smul_fieldToDeRham X π n z v).trans ?_
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]; rfl

/-- The coordinates of `ℂ ⊗[ℚ] V` in a `ℚ`-basis of `ℂ` are the tensor components. -/
lemma finsuppScalarLeft_rTensor_repr_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι ℚ ℂ) (x : ℂ ⊗[ℚ] V) (i : ι) :
    TensorProduct.finsuppScalarLeft ℚ V ι (LinearMap.rTensor V b.repr.toLinearMap x) i =
      TensorProduct.lid ℚ V (LinearMap.rTensor V (b.coord i) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z v =>
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.finsuppScalarLeft_apply_tmul_apply,
      TensorProduct.lid_tmul, Module.Basis.coord_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, map_add]

omit [IsIntegral X.left] [Smooth X.hom] in
/-- A map of constant sheaves sends a constant global section to the constant section of the
image value. -/
lemma constantFunctor_map_constSection {A B : AddCommGrpCat.{0}} (g : A ⟶ B) (a : A) :
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map g).hom.app (op ⊤)
        (constSection (T := TopCat.of (ComplexPoint X)) A ⊤ a) =
      constSection (T := TopCat.of (ComplexPoint X)) B ⊤ (g a) := by
  have h := NatTrans.congr_app
    (toSheafify_naturality (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    ((Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).map g)) (op ⊤)
  have h' := ConcreteCategory.congr_hom h a
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h'
  exact h'.symm.trans rfl

omit [IsIntegral X.left] [Smooth X.hom] in
lemma complexScalarComplexInt_eq_fieldScalarComplex (c : ℂ) :
    complexScalarComplexInt X c = fieldScalarComplex ℂ X c := rfl

/-- `H^0(X; ℂ) → H_dR^0(X)`, the comparison through the Poincaré lemma. -/
def complexH0ToDeRham : H^0(X; ℂ) ≃+ H_dR^((0 : ℕ) : ℤ)(X) :=
  (hypercohomologyAddEquivConstantCohomology ℂ X 0).symm.trans
    (complexConstantCohomologyDeRhamAddEquiv X ((0 : ℕ) : ℤ))

lemma fieldToDeRhamCohomology_eq_complexH0ToDeRham (v : H^0(X; ℚ)) :
    fieldToDeRhamCohomology ℚ X 0 v =
      complexH0ToDeRham X (Sheaf.H.map.{0} (fieldToComplexConstantSheaf ℚ X) 0 v) := by
  change hypercohomologyMap X (fieldToComplexConstantSheafComplexInt ℚ X ≫
      constantsToHolomorphicDeRhamComplexInt X) ((0 : ℕ) : ℤ)
      ((hypercohomologyAddEquivConstantCohomology ℚ X 0).symm v) =
    hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) ((0 : ℕ) : ℤ)
      ((hypercohomologyAddEquivConstantCohomology ℂ X 0).symm
        (Sheaf.H.map.{0} (fieldToComplexConstantSheaf ℚ X) 0 v))
  rw [hypercohomologyAddEquivConstantCohomology_symm_map, hypercohomologyMap_comp_apply]
  rfl

lemma complexH0ToDeRham_smul (c : ℂ) (w : H^0(X; ℂ)) :
    complexH0ToDeRham X (c • w) = c • complexH0ToDeRham X w := by
  change hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) ((0 : ℕ) : ℤ)
      ((hypercohomologyAddEquivConstantCohomology ℂ X 0).symm (c • w)) =
    hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X c) ((0 : ℕ) : ℤ)
      (hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) ((0 : ℕ) : ℤ)
        ((hypercohomologyAddEquivConstantCohomology ℂ X 0).symm w))
  rw [hypercohomologyAddEquivConstantCohomology_symm_smul, ← hypercohomologyMap_comp_apply,
    ← hypercohomologyMap_comp_apply, constantsToHolomorphicDeRhamComplexInt_scalar,
    complexScalarComplexInt_eq_fieldScalarComplex]

end ReadBack

theorem spec_injective_bettiDeRhamHQ_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (n : ℕ) :
    Function.Injective (bettiDeRhamHQ X n) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  let b := Module.Free.chooseBasis ℚ ℂ
  have hinj : Function.Injective fun y : ℂ ⊗[ℚ] HQ X n =>
      TensorProduct.finsuppScalarLeft ℚ (HQ X n) _ (LinearMap.rTensor _ b.repr.toLinearMap y) :=
    (TensorProduct.finsuppScalarLeft ℚ (HQ X n) _).injective.comp
      (LinearEquiv.rTensor (HQ X n) b.repr).injective
  apply hinj
  simp only [map_zero]
  ext i
  rw [finsuppScalarLeft_rTensor_repr_apply, ← deRhamReadBack_bettiDeRhamHQ, hx, map_zero,
    Finsupp.zero_apply]
  rfl

theorem spec_bijective_bettiDeRhamHQ_iff_finrank_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (hF : FiniteBetti X) (n : ℕ) :
    Function.Bijective (bettiDeRhamHQ X n) ↔
      Module.Finite ℂ H_dR^(n : ℤ)(X) ∧
        Module.finrank ℂ H_dR^(n : ℤ)(X) = Module.finrank ℚ (HQ X n) := by
  have := hF.finite n
  have hinj := spec_injective_bettiDeRhamHQ_aux X n
  have hdim : Module.finrank ℂ (ℂ ⊗[ℚ] HQ X n) = Module.finrank ℚ (HQ X n) :=
    Module.finrank_baseChange
  constructor
  · intro hb
    let e := LinearEquiv.ofBijective (bettiDeRhamHQ X n) hb
    exact ⟨Module.Finite.equiv e, e.finrank_eq.symm.trans hdim⟩
  · rintro ⟨hfin, hr⟩
    exact ⟨hinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdim.trans hr.symm)).mp hinj⟩

theorem spec_bettiDeRhamIso_iff_finrank_abelian_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    BettiDeRhamIso X ↔ ∀ n : ℕ,
      Module.Finite ℂ H_dR^(n : ℤ)(X) ∧
        Module.finrank ℂ H_dR^(n : ℤ)(X) = (2 * dim X.left).choose n := by
  have hF := finiteBetti_abelian X
  constructor
  · intro h n
    rw [← finrank_HQ_abelian X n]
    exact (spec_bijective_bettiDeRhamHQ_iff_finrank_aux X hF n).mp (h.bijective n)
  · intro h
    refine ⟨fun n => (spec_bijective_bettiDeRhamHQ_iff_finrank_aux X hF n).mpr ?_⟩
    rw [finrank_HQ_abelian X n]
    exact h n

theorem spec_bettiDeRhamHQ_unit_ne_zero_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] :
    bettiDeRhamHQ X 0 ((1 : ℂ) ⊗ₜ[ℚ] (unitClass X : HQ X 0)) ≠ 0 := by
  classical
  have key : ∀ v : HQ X 0, v ≠ 0 → bettiDeRhamHQ X 0 ((1 : ℂ) ⊗ₜ[ℚ] v) ≠ 0 := by
    intro v hv h
    let b := Module.Free.chooseBasis ℚ ℂ
    obtain ⟨i, hi⟩ : ∃ i, b.coord i 1 ≠ 0 := by
      by_contra! H
      exact one_ne_zero (b.ext_elem fun i => by rw [← b.coord_apply, H i, map_zero,
        Finsupp.zero_apply])
    have h' := deRhamReadBack_bettiDeRhamHQ X (b.coord i) 0 ((1 : ℂ) ⊗ₜ[ℚ] v)
    rw [h, map_zero, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h'
    exact hv ((smul_eq_zero.mp h'.symm).resolve_left hi)
  exact key _ (unitClass_ne_zero' X)

theorem spec_bijective_bettiDeRhamHQ_zero_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] :
    Function.Bijective (bettiDeRhamHQ X 0) := by
  have : PathConnectedSpace (ComplexPoint X) := HodgeLean.Foundations.pathConnectedSpace_complexPoint X
  have : PreconnectedSpace (TopCat.of (ComplexPoint X)) :=
    (inferInstance : PreconnectedSpace (ComplexPoint X))
  refine ⟨spec_injective_bettiDeRhamHQ_aux X 0, fun y => ?_⟩
  let eQ := Sheaf.H.equiv₀
    ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).obj (AddCommGrpCat.of ℚ)) Limits.isTerminalTop
  let eC := Sheaf.H.equiv₀
    ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).obj (AddCommGrpCat.of ℂ)) Limits.isTerminalTop
  let v₀ : HQ X 0 := eQ.symm (constSection (T := TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ) ⊤ 1)
  obtain ⟨w, rfl⟩ := (complexH0ToDeRham X).surjective y
  obtain ⟨a, ha⟩ := exists_eq_constSection (AddCommGrpCat.of ℂ) (eC w)
  refine ⟨a ⊗ₜ v₀, ?_⟩
  rw [bettiDeRhamHQ_tmul, fieldToDeRhamCohomology_eq_complexH0ToDeRham, ← complexH0ToDeRham_smul]
  congr 1
  apply eC.injective
  rw [ha, field_smul_eq, ← Sheaf.H.equiv₀_naturality, Sheaf.H.equiv₀_symm_naturality,
    eC.apply_symm_apply, constantFunctor_map_constSection, constantFunctor_map_constSection]
  congr 1
  change a * algebraMap ℚ ℂ 1 = a
  rw [map_one, mul_one]

end HodgeLean.Adapters

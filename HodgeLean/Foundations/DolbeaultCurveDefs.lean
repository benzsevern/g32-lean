import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.AnalyticSheaf
import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.ManifoldOrientation
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! # Smooth functions, smooth `(0,1)`-forms and `∂̄` on `X(ℂ)` (FROZEN DEFINITIONS)

The real `C^∞` structure on the complex points of a smooth complex scheme, the sheaf `𝒜^{0,0}` of
smooth complex-valued functions, the sheaf `𝒜^{0,1}` of smooth `(0,1)`-forms, the sheaf `𝒪` of
holomorphic functions as a sheaf of abelian groups, the inclusion `𝒪 ⟶ 𝒜^{0,0}` and the Dolbeault
operator `∂̄ : 𝒜^{0,0} ⟶ 𝒜^{0,1}`, all as morphisms of `AnalyticAdditiveSheaf X`.

A `(0,1)`-form at `x` is a real-linear map `ℂ^d → ℂ` (the tangent space in the chart at `x`) that
is conjugate-linear; it is smooth when its expression in the tangent coordinates of one fixed chart
is a smooth function of the base point. Conjugate-linearity does not depend on the chart, because
the chart changes of `X(ℂ)` are holomorphic. `∂̄ f` is the conjugate-linear part of the real
differential of `f`.
-/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicGeometry ComplexPoint Topology
open scoped ContDiff Manifold

namespace HodgeLean.Foundations

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Multiplication by `i` on a complex vector space `E`, as a real linear map: the complex structure
`J` of the underlying real space.
Source: Huybrechts, *Complex Geometry*, Universitext (2005), §1.2 (linear algebra of a complex
structure `I` on a real vector space). -/
def complexStructure : E →L[ℝ] E :=
  (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

@[simp] lemma complexStructure_apply (v : E) : complexStructure v = Complex.I • v := rfl

example (v : E) : complexStructure (complexStructure v) = -v := by
  simp [smul_smul]

/-- The conjugate-linear part `L ↦ (L + i L ∘ J) / 2` of a real-linear map `L : E → ℂ`. Every real
linear map is the sum of a complex-linear and a conjugate-linear part; for the real differential of
a function this part is `∂̄ f`.
Source: Huybrechts, *Complex Geometry*, §1.2 (the decomposition `V^*_ℂ = V^{*1,0} ⊕ V^{*0,1}`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (`d = ∂ + ∂̄` on functions). -/
def antiLinearPart : (E →L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] ℂ) :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ (E →L[ℝ] ℂ) +
    ContinuousLinearMap.compL ℝ E ℂ ℂ ((Complex.I • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ)
      ∘L (ContinuousLinearMap.compL ℝ E E ℂ).flip complexStructure)

lemma antiLinearPart_apply (L : E →L[ℝ] ℂ) (v : E) :
    antiLinearPart L v = (2⁻¹ : ℝ) • (L v + Complex.I * L (Complex.I • v)) := by
  simp [antiLinearPart]

lemma antiLinearPart_apply_I_smul (L : E →L[ℝ] ℂ) (v : E) :
    antiLinearPart L (Complex.I • v) = -(Complex.I * antiLinearPart L v) := by
  rw [antiLinearPart_apply, antiLinearPart_apply, smul_smul, Complex.I_mul_I, neg_one_smul,
    map_neg]
  simp only [Complex.real_smul]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma antiLinearPart_antiLinearPart (L : E →L[ℝ] ℂ) :
    antiLinearPart (antiLinearPart L) = antiLinearPart L := by
  ext v
  rw [antiLinearPart_apply (antiLinearPart L), antiLinearPart_apply_I_smul]
  simp only [Complex.real_smul]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma antiLinearPart_restrictScalars (g : E →L[ℂ] ℂ) :
    antiLinearPart (g.restrictScalars ℝ) = 0 := by
  ext v
  rw [antiLinearPart_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul,
    zero_apply]
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  exact smul_zero _

lemma antiLinearPart_comp_restrictScalars (L : E →L[ℝ] ℂ) (T : E →L[ℂ] E) :
    antiLinearPart (L ∘L T.restrictScalars ℝ) = antiLinearPart L ∘L T.restrictScalars ℝ := by
  ext v
  simp [antiLinearPart_apply, map_smul]

/-- The conjugate-linear part of a complex-linear functional is zero. -/
example : antiLinearPart ((ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ) = 0 :=
  antiLinearPart_restrictScalars _

end Linear

section Manifold

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- After restricting scalars, the complex points of a smooth complex scheme of relative dimension
`d` form a real `C^∞` manifold on the same holomorphic charts (upstream proves `C^1`).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (a complex manifold is a
smooth manifold); upstream `contDiffOn_localChart_transition` and `isRealManifold_one`. -/
instance isRealManifold_infty [SmoothOfRelativeDimension d X.hom] :
    IsManifold 𝓘(ℝ, Fin d → ℂ) ∞ (ComplexPoint X) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨z, rfl⟩ := he
  obtain ⟨z', rfl⟩ := he'
  have h := (contDiffOn_localChart_transition X d z z').restrict_scalars ℝ
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    CompTriple.comp_eq, Function.id_comp, Function.comp_id, Set.preimage_id,
    Set.range_id, Set.inter_univ] using h.of_le (by simp)

example [SmoothOfRelativeDimension d X.hom] : IsManifold 𝓘(ℝ, Fin d → ℂ) 2 (ComplexPoint X) :=
  inferInstance

/-- `ℂ`, as a real manifold, is a smooth ring: multiplication is real-bilinear, hence smooth.
Source: Mathlib's `instFieldContMDiffRing`, with `ℝ` in place of `ℂ` as scalar field. -/
instance complexContMDiffRing {n : ℕ∞ω} : ContMDiffRing 𝓘(ℝ, ℂ) n ℂ :=
  { instNormedSpaceLieAddGroup with
    contMDiff_mul := by
      rw [contMDiff_iff]
      refine ⟨continuous_mul, fun x y => ?_⟩
      simp only [mfld_simps]
      rw [contDiffOn_univ]
      exact contDiff_mul }

example : ContMDiffRing 𝓘(ℝ, ℂ) ∞ ℂ := inferInstance

/-- Extension by zero of a function on a subset `U ⊆ M` to all of `M`. Only its germs at points of
an open `U` are used.
Source: elementary; used to compare sections over different opens. -/
def extendSection {M F : Type*} [Zero F] {U : Set M} (f : U → F) : M → F := by
  classical exact fun y => if h : y ∈ U then f ⟨y, h⟩ else 0

lemma extendSection_of_mem {M F : Type*} [Zero F] {U : Set M} (f : U → F) {y : M}
    (h : y ∈ U) : extendSection f y = f ⟨y, h⟩ := by
  simp [extendSection, h]

example {M : Type*} {U : Set M} (y : M) (h : y ∉ U) :
    extendSection (fun _ : U => (1 : ℂ)) y = 0 := by
  simp [extendSection, h]

lemma extendSection_eventuallyEq {M F : Type*} [TopologicalSpace M] [Zero F] {U V : Opens M}
    (i : U ≤ V) (f : V → F) {x : M} (hx : x ∈ U) :
    extendSection (fun y : U => f ⟨y, i y.2⟩) =ᶠ[𝓝 x] extendSection f := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  rw [extendSection_of_mem _ hy, extendSection_of_mem _ (i hy)]

variable [SmoothOfRelativeDimension d X.hom]

/-- A family `σ y : ℂ^d → ℂ` of real-linear maps (`σ y` acting on the tangent space at `y` in the
chart at `y`) is a smooth `(0,1)`-form at `x` when `σ x` is conjugate-linear and, written in the
tangent coordinates of the chart at `x` (by composing with the tangent coordinate change), it is a
`C^∞` function of the base point near `x`. This is smoothness at `x` of a section of the bundle
`Hom_ℝ(T X(ℂ), ℂ)`, in Mathlib's trivialization, together with the type condition.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (forms of type `(p, q)`);
Huybrechts, *Complex Geometry*, §1.3 and §2.6 (the bundle `Λ^{0,1}` and its smooth sections). -/
def IsZeroOneFormAt (σ : ComplexPoint X → (Fin d → ℂ) →L[ℝ] ℂ) (x : ComplexPoint X) : Prop :=
  antiLinearPart (σ x) = σ x ∧
    ContMDiffAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, (Fin d → ℂ) →L[ℝ] ℂ) ∞
      (fun y => σ y ∘L tangentCoordChange 𝓘(ℝ, Fin d → ℂ) x y y) x

variable {X d} in
lemma IsZeroOneFormAt.congr {σ σ' : ComplexPoint X → (Fin d → ℂ) →L[ℝ] ℂ} {x : ComplexPoint X}
    (h : IsZeroOneFormAt X d σ x) (h' : σ =ᶠ[𝓝 x] σ') : IsZeroOneFormAt X d σ' x := by
  refine ⟨h'.eq_of_nhds ▸ h.1, h.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [h'] with y hy
  rw [hy]

example (x : ComplexPoint X) : IsZeroOneFormAt X d (fun _ => 0) x :=
  ⟨map_zero _, by simpa using contMDiffAt_const⟩

/-- Being a smooth `(0,1)`-form at every point is a local condition on sections over opens of
`X(ℂ)`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2; Mathlib's
`TopCat.LocalPredicate`. -/
def zeroOneFormPredicate :
    TopCat.LocalPredicate (fun _ : TopCat.of (ComplexPoint X) => (Fin d → ℂ) →L[ℝ] ℂ) where
  pred {U} σ := ∀ x : U, IsZeroOneFormAt X d (extendSection σ) x
  res {U V} i σ h x :=
    (h ⟨x, i.le x.2⟩).congr (extendSection_eventuallyEq i.le σ x.2).symm
  locality {U} σ h x := by
    obtain ⟨V, hxV, i, hV⟩ := h x
    exact (hV ⟨x, hxV⟩).congr (extendSection_eventuallyEq i.le σ hxV)

lemma extendSection_add {M F : Type*} [AddZeroClass F] {U : Set M} (f g : U → F) :
    extendSection (f + g) = extendSection f + extendSection g := by
  funext y
  by_cases h : y ∈ U <;> simp [extendSection, h]

lemma extendSection_neg {M F : Type*} [NegZeroClass F] {U : Set M} (f : U → F) :
    extendSection (-f) = -extendSection f := by
  funext y
  by_cases h : y ∈ U <;> simp [extendSection, h]

lemma extendSection_zero {M F : Type*} [Zero F] {U : Set M} :
    extendSection (0 : U → F) = 0 := by
  funext y
  by_cases h : y ∈ U <;> simp [extendSection, h]

/-- Smooth `(0,1)`-forms on an open `U ⊆ X(ℂ)`, as an additive subgroup of all sections.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2. -/
def zeroOneFormSubgroup (U : Opens (TopCat.of (ComplexPoint X))) :
    AddSubgroup (∀ _ : U, (Fin d → ℂ) →L[ℝ] ℂ) where
  carrier := {σ | (zeroOneFormPredicate X d).pred σ}
  zero_mem' x := by
    refine ⟨by rw [extendSection_zero]; simp, ?_⟩
    rw [extendSection_zero]
    simpa using contMDiffAt_const
  add_mem' {σ τ} hσ hτ x := by
    refine ⟨by rw [extendSection_add, Pi.add_apply, map_add, (hσ x).1, (hτ x).1], ?_⟩
    rw [extendSection_add]
    refine ((hσ x).2.add (hτ x).2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, ContinuousLinearMap.add_comp]
  neg_mem' {σ} hσ x := by
    refine ⟨by rw [extendSection_neg, Pi.neg_apply, map_neg, (hσ x).1], ?_⟩
    rw [extendSection_neg]
    simpa only [Pi.neg_apply, ContinuousLinearMap.neg_comp] using (hσ x).2.neg

/-- The presheaf of abelian groups of smooth `(0,1)`-forms on opens of `X(ℂ)`, with restriction of
sections.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2. -/
def zeroOneFormPresheaf (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) where
  obj U := AddCommGrpCat.of (zeroOneFormSubgroup X d U.unop)
  map {_ _} i := AddCommGrpCat.ofHom
    { toFun := fun σ => ⟨fun x => σ.1 ⟨x.1, i.unop.le x.2⟩,
        (zeroOneFormPredicate X d).res i.unop σ.1 σ.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sheaf `𝒜^{0,1}` of smooth `(0,1)`-forms on `X(ℂ)`, as a sheaf of abelian groups. Its
sheaf condition is that of the local predicate `zeroOneFormPredicate`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the sheaf `𝒜^{p,q}`) and
§3 (Dolbeault's theorem); Mathlib's `TopCat.subsheafToTypes`. -/
def zeroOneFormSheaf (d : ℕ) [SmoothOfRelativeDimension d X.hom] : AnalyticAdditiveSheaf X where
  obj := zeroOneFormPresheaf X d
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat)]
    exact (TopCat.subsheafToTypes (zeroOneFormPredicate X d)).property

example (d : ℕ) [SmoothOfRelativeDimension d X.hom] (U : Opens (ComplexPoint X)) :
    (zeroOneFormSheaf X d).obj.obj (Opposite.op U) = AddCommGrpCat.of (zeroOneFormSubgroup X d U) :=
  rfl

variable {X d} in
/-- The conjugate-linear part of the differential of a smooth function is a smooth `(0,1)`-form. -/
lemma isZeroOneFormAt_antiLinearPart_mfderiv {g : ComplexPoint X → ℂ} {x : ComplexPoint X}
    (hg : ContMDiffAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ∞ g x) :
    IsZeroOneFormAt X d (fun y => antiLinearPart (mfderiv 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) g y)) x := by
  refine ⟨antiLinearPart_antiLinearPart _, ?_⟩
  have h1 := hg.mfderiv_const (m := ∞) (by simp)
  have h2 : ContMDiffAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, (Fin d → ℂ) →L[ℝ] ℂ) ∞
      (fun y => antiLinearPart (inTangentCoordinates 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) id g
        (fun y => mfderiv 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) g y) x y)) x :=
    antiLinearPart.contDiff.comp_contMDiffAt h1
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt (Fin d → ℂ) x).open_source.mem_nhds (mem_chart_source _ x)] with y hy
  have e1 := inTangentCoordinates_eq (I := 𝓘(ℝ, Fin d → ℂ)) (I' := 𝓘(ℝ, ℂ)) id g
    (fun y => mfderiv 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) g y) (x₀ := x) (x := y) hy (by simp)
  have e2 := realTangentCoordChange_eq_restrictScalars X d x y y hy (mem_localChart_source X d y)
  have e3 : tangentCoordChange 𝓘(ℝ, ℂ) (g y) (g x) (g y) = ContinuousLinearMap.id ℝ ℂ := by
    simp
    rfl
  rw [e1]
  change antiLinearPart (mfderiv 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) g y) ∘L
      tangentCoordChange 𝓘(ℝ, Fin d → ℂ) x y y =
    antiLinearPart (tangentCoordChange 𝓘(ℝ, ℂ) (g y) (g x) (g y) ∘L
      mfderiv 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) g y ∘L tangentCoordChange 𝓘(ℝ, Fin d → ℂ) x y y)
  rw [e3, e2, ContinuousLinearMap.id_comp]
  exact (antiLinearPart_comp_restrictScalars _ _).symm

/-- The presheaf of abelian groups of real-smooth complex-valued functions on opens of `X(ℂ)`.
Source: Mathlib's `smoothSheaf` and `smoothPresheafCommRing`, for the real `C^∞` structure
`isRealManifold_infty`. -/
def smoothFunctionPresheaf (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) where
  obj U := AddCommGrpCat.of
    ((smoothSheaf 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) (ComplexPoint X) ℂ).presheaf.obj U)
  map h := AddCommGrpCat.ofHom
    (ContMDiffMap.restrictRingHom 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ℂ
      (CategoryTheory.leOfHom h.unop)).toAddMonoidHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sheaf `𝒜^{0,0}` of real-smooth complex-valued functions on `X(ℂ)`, as a sheaf of abelian
groups.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2–3 (the sheaf `𝒜^{0,0}` of
`C^∞` functions); Mathlib's `smoothSheaf`. -/
def smoothFunctionSheaf (d : ℕ) [SmoothOfRelativeDimension d X.hom] : AnalyticAdditiveSheaf X where
  obj := smoothFunctionPresheaf X d
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat)]
    exact (smoothSheaf 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) (ComplexPoint X) ℂ).property

/-- Sections over `U` are the smooth maps `U → ℂ`. -/
example (d : ℕ) [SmoothOfRelativeDimension d X.hom] (U : Opens (ComplexPoint X)) :
    ((smoothFunctionSheaf X d).obj.obj (Opposite.op U) : Type) =
      C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯ :=
  rfl

/-- The presheaf of abelian groups of holomorphic functions on opens of `X(ℂ)`: upstream's
`holomorphicFunctionPresheaf` with its additive structure only.
Source: upstream `holomorphicFunctionSheafToTypes` and `holomorphicFunctionPresheaf`. -/
def holomorphicFunctionAddPresheaf (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) where
  obj U := AddCommGrpCat.of ((holomorphicFunctionSheafToTypes X d).presheaf.obj U)
  map h := AddCommGrpCat.ofHom
    (ContMDiffMap.restrictRingHom 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ℂ
      (CategoryTheory.leOfHom h.unop)).toAddMonoidHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sheaf `𝒪` of holomorphic functions on `X(ℂ)`, as a sheaf of abelian groups.
Source: upstream `holomorphicFunctionSheaf` (`ComplexPoint/AnalyticSheaf.lean`), forgetting the
ring structure. -/
def holomorphicFunctionAddSheaf (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    AnalyticAdditiveSheaf X where
  obj := holomorphicFunctionAddPresheaf X d
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat)]
    exact (holomorphicFunctionSheafToTypes X d).property

/-- Sections over `U` are the holomorphic maps `U → ℂ`. -/
example (d : ℕ) [SmoothOfRelativeDimension d X.hom] (U : Opens (ComplexPoint X)) :
    ((holomorphicFunctionAddSheaf X d).obj.obj (Opposite.op U) : Type) =
      C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯ :=
  rfl

/-- A holomorphic function is real-smooth. -/
lemma contMDiff_real_of_complex {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℂ} (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω f) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f := by
  rw [contMDiff_iff] at hf ⊢
  exact ⟨hf.1, fun x y => ((hf.2 x y).restrict_scalars ℝ).of_le le_top⟩

/-- The inclusion `𝒪 ⟶ 𝒜^{0,0}`: a holomorphic function is real-smooth, and is sent to itself.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the first map of the
Dolbeault sequence `0 → 𝒪 → 𝒜^{0,0} → 𝒜^{0,1}`). -/
def holomorphicToSmooth (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    holomorphicFunctionAddSheaf X d ⟶ smoothFunctionSheaf X d :=
  ⟨{ app U := AddCommGrpCat.ofHom
      { toFun := fun f => (⟨f.1, contMDiff_real_of_complex f.2⟩ :
          C^∞⟮𝓘(ℝ, Fin d → ℂ), (Opposite.unop U : Opens (ComplexPoint X)); 𝓘(ℝ, ℂ), ℂ⟯)
        map_zero' := rfl
        map_add' _ _ := rfl }
     naturality _ _ _ := rfl }⟩

/-- The inclusion does not change the underlying function. -/
example (d : ℕ) [SmoothOfRelativeDimension d X.hom] (U : Opens (ComplexPoint X))
    (f : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) :
    (((holomorphicToSmooth X d).hom.app (Opposite.op U)) f).1 = f :=
  rfl

variable {X d} in
lemma contMDiffAt_extendSection {U : Opens (ComplexPoint X)}
    (f : C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) (x : U) :
    ContMDiffAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ∞ (extendSection f) x := by
  rw [← contMDiffAt_subtype_iff]
  have : (fun y : U => extendSection f y) = f := funext fun y => extendSection_of_mem _ y.2
  rw [this]
  exact f.contMDiff.contMDiffAt

/-- The real differential at `x` of a complex-valued function on `X(ℂ)`, as a real-linear map on the
tangent space at `x` in the chart at `x`.
Source: Mathlib's `mfderiv`, for the real `C^∞` structure `isRealManifold_infty`. -/
def realDifferential (g : ComplexPoint X → ℂ) (x : ComplexPoint X) : (Fin d → ℂ) →L[ℝ] ℂ :=
  mfderiv 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) g x

example (x : ComplexPoint X) : realDifferential X d (fun _ => (1 : ℂ)) x = 0 :=
  mfderiv_const

variable {X d} in
lemma realDifferential_congr {g g' : ComplexPoint X → ℂ} {x : ComplexPoint X}
    (h : g =ᶠ[𝓝 x] g') : realDifferential X d g x = realDifferential X d g' x := by
  unfold realDifferential
  rw [h.mfderiv_eq]
  rfl

variable {X d} in
lemma realDifferential_add {g g' : ComplexPoint X → ℂ} {x : ComplexPoint X}
    (hg : MDifferentiableAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) g x)
    (hg' : MDifferentiableAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) g' x) :
    realDifferential X d (g + g') x = realDifferential X d g x + realDifferential X d g' x :=
  mfderiv_add hg hg'

variable {X d} in
lemma realDifferential_const (c : ℂ) (x : ComplexPoint X) :
    realDifferential X d (fun _ => c) x = 0 :=
  mfderiv_const

/-- `∂̄ f` for a smooth function `f` on an open `U ⊆ X(ℂ)`: at `x ∈ U`, the conjugate-linear part
of the real differential of `f` at `x`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (`∂̄ f = Σ ∂f/∂z̄ᵢ dz̄ᵢ`). -/
def dbarSection {U : Opens (ComplexPoint X)} (f : C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) :
    ∀ _ : U, (Fin d → ℂ) →L[ℝ] ℂ :=
  fun x => antiLinearPart (realDifferential X d (extendSection f) x)

lemma dbarSection_mem {U : Opens (ComplexPoint X)} (f : C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) :
    dbarSection X d f ∈ zeroOneFormSubgroup X d U := fun x =>
  (isZeroOneFormAt_antiLinearPart_mfderiv (contMDiffAt_extendSection f x)).congr <| by
    filter_upwards [U.isOpen.mem_nhds x.2] with y hy
    rw [extendSection_of_mem _ hy]
    rfl

lemma dbarSection_add {U : Opens (ComplexPoint X)}
    (f g : C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) :
    dbarSection X d (f + g) = dbarSection X d f + dbarSection X d g := by
  funext x
  have hf := (contMDiffAt_extendSection f x).mdifferentiableAt (by simp)
  have hg := (contMDiffAt_extendSection g x).mdifferentiableAt (by simp)
  have : extendSection (⇑(f + g)) = extendSection f + extendSection g := extendSection_add _ _
  simp only [dbarSection, Pi.add_apply, this, realDifferential_add hf hg, map_add]

lemma dbarSection_zero {U : Opens (ComplexPoint X)} :
    dbarSection X d (0 : C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) = 0 := by
  funext x
  have : extendSection (⇑(0 : C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯)) = fun _ => (0 : ℂ) :=
    extendSection_zero
  simp only [dbarSection, Pi.zero_apply, this, realDifferential_const, map_zero]

lemma dbarSection_restrict {U V : Opens (ComplexPoint X)} (i : V ≤ U)
    (f : C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) (x : V) :
    dbarSection X d (ContMDiffMap.restrictRingHom 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ℂ i f) x =
      dbarSection X d f ⟨x, i x.2⟩ := by
  simp only [dbarSection]
  exact congrArg antiLinearPart (realDifferential_congr (extendSection_eventuallyEq i f x.2))

/-- The Dolbeault operator `∂̄ : 𝒜^{0,0} ⟶ 𝒜^{0,1}` on `X(ℂ)`, as a morphism of sheaves of abelian
groups. That `∂̄ f` is a smooth `(0,1)`-form is `dbarSection_mem`: the differential of a smooth
function is smooth in tangent coordinates (Mathlib's `ContMDiffAt.mfderiv_const`), and the chart
changes are complex-linear (`realTangentCoordChange_eq_restrictScalars`).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2–3 (the Dolbeault sequence
`0 → 𝒪 → 𝒜^{0,0} → 𝒜^{0,1} → 0` on a Riemann surface). -/
def dbar (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    smoothFunctionSheaf X d ⟶ zeroOneFormSheaf X d :=
  ⟨{ app U := AddCommGrpCat.ofHom
      { toFun := fun f => ⟨dbarSection X d f, dbarSection_mem X d f⟩
        map_zero' := Subtype.ext (dbarSection_zero X d)
        map_add' f g := Subtype.ext (dbarSection_add X d f g) }
     naturality U V i := by
      ext f
      exact Subtype.ext (funext fun x => (dbarSection_restrict X d i.unop.le f x)) }⟩

/-- On sections, `∂̄` is `dbarSection`. -/
example (d : ℕ) [SmoothOfRelativeDimension d X.hom] (U : Opens (ComplexPoint X))
    (f : C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) :
    (((dbar X d).hom.app (Opposite.op U)) f).1 = dbarSection X d f :=
  rfl

end Manifold

end HodgeLean.Foundations

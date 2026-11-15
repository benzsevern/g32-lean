import HodgeLean.Adapters.HodgeDegreeOneAbelianDefs
import HodgeLean.Adapters.HolomorphicPeriodsDeRham
import HodgeLean.Adapters.HolomorphicPeriodsOnX
import HodgeLean.Adapters.HolomorphicPeriods
import HodgeLean.Adapters.HolomorphicFormsPullback
import HodgeLean.Adapters.UniformizationBiholomorphic
import HodgeLean.Adapters.HodgeFilterLattice

/-! # Proof obligations for `HodgeDegreeOneAbelian`

One `_aux` per statement of `HodgeLean.Adapters.HodgeDegreeOneAbelian`, all open.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

open scoped Manifold ContDiff in
theorem spec_exists_local_expPrimitive_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (a : (Fin d → ℂ) →L[ℂ] ℂ) (x : ComplexPoint X) :
    ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U)
      (f : OpenHolomorphicFunctions X d (op U)),
      ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
        HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul) a v := by
  obtain ⟨v₀, hv₀⟩ := surjective_complexExponential X d (Additive.ofMul x)
  obtain ⟨e, hv₀e, heq, hs⟩ := spec_complexExponential_localBiholomorph X d v₀
  have hexp : Continuous (fun w ↦ (complexExponential X d w).toMul) :=
    (spec_mdifferentiable_complexExponential X d).continuous
  have hsec : ∀ y ∈ e.target, (complexExponential X d (e.symm y)).toMul = y := fun y hy ↦
    (heq (e.map_target hy)).trans (e.right_inv hy)
  let U : Opens (TopCat.of (ComplexPoint X)) := ⟨e.target, e.open_target⟩
  have hxU : x ∈ U := by
    change x ∈ e.target
    have hx : x = e v₀ := by
      rw [← heq hv₀e]
      change x = (complexExponential X d v₀).toMul
      rw [hv₀]
      rfl
    rw [hx]
    exact e.map_source hv₀e
  have hfa : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω
      (fun y : (U : Opens (ComplexPoint X)) ↦ a (e.symm y.1)) := by
    intro y
    have h1 : ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω (fun y ↦ a (e.symm y)) e.target :=
      a.contDiff.contMDiff.comp_contMDiffOn hs
    exact (contMDiffAt_subtype_iff (U := (U : Opens (ComplexPoint X))) (x := y)).mpr
      ((h1 y.1 y.2).contMDiffAt (e.open_target.mem_nhds y.2))
  let f : OpenHolomorphicFunctions X d (op U) := ⟨fun y ↦ a (e.symm y.1), hfa⟩
  refine ⟨U, hxU, f, fun v hv ↦ ?_⟩
  obtain ⟨e', hve', heq', hs'⟩ := spec_complexExponential_localBiholomorph X d v
  have hsec' : ∀ y ∈ e'.target, (complexExponential X d (e'.symm y)).toMul = y := fun y hy ↦
    (heq' (e'.map_target hy)).trans (e'.right_inv hy)
  have hv' : (complexExponential X d v).toMul ∈ e'.target := by
    rw [show (complexExponential X d v).toMul = e' v from heq' hve']
    exact e'.map_source hve'
  have hev := spec_eventually_sub_eq_of_complexExponential X d e.target e'.target e.symm e'.symm
    e.open_target e'.open_target e.continuousOn_symm e'.continuousOn_symm hsec hsec'
    _ ⟨hv, hv'⟩
  have hev2 := hexp.continuousAt.tendsto.eventually hev
  have hsrc : ∀ᶠ w in nhds v, w ∈ e'.source := e'.open_source.mem_nhds hve'
  have htgt : ∀ᶠ w in nhds v, (complexExponential X d w).toMul ∈ e.target :=
    hexp.continuousAt.tendsto.eventually (e.open_target.mem_nhds hv)
  refine (a.hasFDerivAt.add_const (a (e.symm (complexExponential X d v).toMul -
    e'.symm (complexExponential X d v).toMul))).congr_of_eventuallyEq ?_
  filter_upwards [hev2, hsrc, htgt] with w hw hws hwt
  have hw' : e'.symm (complexExponential X d w).toMul = w := by
    rw [show (complexExponential X d w).toMul = e' w from heq' hws]
    exact e'.left_inv hws
  change Function.extend Subtype.val f.1 0
    (Subtype.val (⟨(complexExponential X d w).toMul, hwt⟩ : (U : Set (ComplexPoint X)))) = _
  rw [Subtype.val_injective.extend_apply]
  change a (e.symm (complexExponential X d w).toMul) = _
  rw [← hw, hw', ← map_add, add_sub_cancel]

open scoped Manifold ContDiff in
/-- `d f` in a chart is the chart derivative of `f`. -/
theorem chartEvaluation_differential_ofFunction (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : Opens (TopCat.of (ComplexPoint X)))
    (z : ComplexPoint X) (f : OpenHolomorphicFunctions X d (op U)) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d (op U) z) (u : Fin d → ℂ) :
    chartEvaluation X d (op U) z 1 (Algebra.DeRham.differential ℂ
        (OpenHolomorphicFunctions X d (op U)) 0
        (Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d (op U)) f)) y (fun _ ↦ u) =
      chartSectionDifferential X d (op U) z f y u := by
  rw [Algebra.DeRham.ofFunction_apply, Algebra.DeRham.differential_mk,
    chartEvaluation_mk X d (op U) z 1 _ _ hy]
  simp only [chartGeneratorEvaluation, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.wedgeCovectors_apply_eq_det, Matrix.det_unique,
    chartSection_apply_of_mem X d (op U) z _ hy]
  change (1 : ℂ) • _ = _
  rw [one_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of `df` is `d` of the restriction. -/
theorem localExactOneForm_map (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] {U V : Opens (TopCat.of (ComplexPoint X))} (i : V ≤ U)
    (f : OpenHolomorphicFunctions X d (op U)) :
    (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE i).op (localExactOneForm X d U f) =
      localExactOneForm X d V (holomorphicRestrictionAlgHom X d (homOfLE i).op f) := by
  have h := ConcreteCategory.congr_hom ((toSheafify (Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))) (holomorphicDeRhamPresheaf X d 1)).naturality (homOfLE i).op)
    (Submodule.Quotient.mk (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d (op U)) 0
      (Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d (op U)) f)))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  refine h.symm.trans ?_
  unfold localExactOneForm
  congr 1
  change Submodule.Quotient.mk (formRestriction X d (homOfLE i).op 1
    (Algebra.DeRham.differential ℂ _ 0 _)) = _
  rw [formRestriction_differential, formRestriction, Algebra.DeRham.map_ofFunction]

/-- The value of the extension of `f` at a point of `U`. -/
theorem extendedSection_apply_of_mem (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (op U)) {p : ComplexPoint X} (hp : p ∈ U) :
    extendedSection X d (op U) f p = f.1 ⟨p, hp⟩ :=
  Subtype.val_injective.extend_apply f.1 0 (⟨p, hp⟩ : (U : Set (ComplexPoint X)))

/-- Two local primitives of the same covector differ by a locally constant function. -/
theorem eventually_extendedSection_sub_eq (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (a : (Fin d → ℂ) →L[ℂ] ℂ) (U U' : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (op U)) (f' : OpenHolomorphicFunctions X d (op U'))
    (hf : ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
      HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul) a v)
    (hf' : ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U' →
      HasFDerivAt (fun w ↦ extendedSection X d (op U') f' (complexExponential X d w).toMul) a v)
    {q : ComplexPoint X} (hq : q ∈ U ⊓ U') :
    ∀ᶠ p in nhds q, extendedSection X d (op U) f p - extendedSection X d (op U') f' p =
      extendedSection X d (op U) f q - extendedSection X d (op U') f' q := by
  obtain ⟨v, hv⟩ := surjective_complexExponential X d (Additive.ofMul q)
  have hvq : (complexExponential X d v).toMul = q := by rw [hv]; rfl
  obtain ⟨e, hve, heq, -⟩ := spec_complexExponential_localBiholomorph X d v
  have hexp : Continuous (fun w ↦ (complexExponential X d w).toMul) :=
    (spec_mdifferentiable_complexExponential X d).continuous
  let G : (Fin d → ℂ) → ℂ := fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul -
    extendedSection X d (op U') f' (complexExponential X d w).toMul
  have hO : IsOpen {w : Fin d → ℂ | (complexExponential X d w).toMul ∈ U ⊓ U'} :=
    (U ⊓ U').isOpen.preimage hexp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO v (by simpa only [Set.mem_ofPred_eq, hvq])
  have hG : ∀ w ∈ Metric.ball v r, HasFDerivAt G 0 w := fun w hw ↦ by
    have hwU := hball hw
    simpa only [sub_self] using (hf w hwU.1).fun_sub (hf' w hwU.2)
  have hconst : ∀ w ∈ Metric.ball v r, G w = G v := fun w hw ↦
    Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball v r).isPreconnected
      (fun w hw ↦ (hG w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hG w hw).fderiv) hw (Metric.mem_ball_self hr)
  have hqt : q ∈ e.target := by
    rw [← hvq, show (complexExponential X d v).toMul = e v from heq hve]
    exact e.map_source hve
  have hsymm : e.symm q = v := by
    rw [← hvq, show (complexExponential X d v).toMul = e v from heq hve]
    exact e.left_inv hve
  have h1 : ∀ᶠ p in nhds q, e.symm p ∈ Metric.ball v r := by
    have := (e.continuousAt_symm hqt).eventually (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hr))
    rwa [hsymm] at this
  filter_upwards [h1, e.open_target.mem_nhds hqt] with p hp hpt
  have hexp_p : (complexExponential X d (e.symm p)).toMul = p :=
    (heq (e.map_target hpt)).trans (e.right_inv hpt)
  have := hconst _ hp
  simp only [G, hexp_p, hvq] at this
  exact this

open scoped Manifold in
theorem spec_localExactOneForm_inf_eq_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (a : (Fin d → ℂ) →L[ℂ] ℂ) (U U' : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (op U)) (f' : OpenHolomorphicFunctions X d (op U'))
    (hf : ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
      HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul) a v)
    (hf' : ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U' →
      HasFDerivAt (fun w ↦ extendedSection X d (op U') f' (complexExponential X d w).toMul) a v) :
    (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op
        (localExactOneForm X d U f) =
      (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op
        (localExactOneForm X d U' f') := by
  rw [localExactOneForm_map, localExactOneForm_map]
  unfold localExactOneForm
  congr 1
  refine (Submodule.Quotient.eq _).2 ?_
  rw [← map_sub, ← map_sub]
  refine (mem_chartEvaluationKernel_iff X d _ 1 _).2 fun z y hy ↦ ?_
  ext m
  rw [show m = fun _ ↦ m 0 from funext fun k ↦ by rw [Subsingleton.elim k 0],
    chartEvaluation_differential_ofFunction X d (U ⊓ U') z _ hy]
  change chartSectionDifferential X d (op (U ⊓ U')) z _ y (m 0) = 0
  suffices h : chartSectionDifferential X d (op (U ⊓ U')) z
      (holomorphicRestrictionAlgHom X d (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op f -
        holomorphicRestrictionAlgHom X d (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op f') y = 0 by
    rw [h]; rfl
  have hq : (extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y ∈ U ⊓ U' := hy.2
  have hev := (continuousAt_extChartAt_symm'' hy.1).eventually
    (eventually_extendedSection_sub_eq X d a U U' f f' hf hf' hq)
  rw [chartSectionDifferential, fderivWithin_of_isOpen (isOpen_chartSectionDomain X d _ z) hy]
  have hc : chartSection X d (op (U ⊓ U')) z
      (holomorphicRestrictionAlgHom X d (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op f -
        holomorphicRestrictionAlgHom X d (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op f') =ᶠ[nhds y]
      fun _ ↦ extendedSection X d (op U) f ((extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y) -
        extendedSection X d (op U') f' ((extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y) := by
    filter_upwards [(isOpen_chartSectionDomain X d _ z).mem_nhds hy, hev] with w hw hwe
    rw [chartSection_apply_of_mem X d _ z _ hw, ← hwe, extendedSection_apply_of_mem X d U f
      (hw.2.1), extendedSection_apply_of_mem X d U' f' hw.2.2]
    rfl
  rw [hc.fderiv_eq, fderiv_const_apply]

set_option backward.isDefEq.respectTransparency false in
theorem spec_exists_globalForm_of_expPrimitive_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (a : (Fin d → ℂ) →L[ℂ] ℂ) :
    ∃ θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤),
      ∀ (U : Opens (TopCat.of (ComplexPoint X))) (f : OpenHolomorphicFunctions X d (op U)),
        (∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
          HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul)
            a v) →
        (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
          localExactOneForm X d U f := by
  choose U hx f hf using fun x ↦ spec_exists_local_expPrimitive_aux X d a x
  obtain ⟨θ, hθ, -⟩ := (holomorphicDeRhamSheaf X d 1).existsUnique_gluing' U ⊤
    (fun _ ↦ homOfLE le_top) (fun x _ ↦ Opens.mem_iSup.2 ⟨x, hx x⟩)
    (fun x ↦ localExactOneForm X d (U x) (f x))
    (fun x y ↦ spec_localExactOneForm_inf_eq_aux X d a (U x) (U y) (f x) (f y) (hf x) (hf y))
  refine ⟨θ, fun V g hg ↦ ?_⟩
  refine (holomorphicDeRhamSheaf X d 1).eq_of_locally_eq' (fun x ↦ V ⊓ U x) V
    (fun _ ↦ homOfLE inf_le_left) (fun p hp ↦ Opens.mem_iSup.2 ⟨p, hp, hx p⟩) _ _ fun x ↦ ?_
  change (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_left : V ⊓ U x ≤ V)).op
      ((holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ) =
    (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_left : V ⊓ U x ≤ V)).op
      (localExactOneForm X d V g)
  rw [spec_localExactOneForm_inf_eq_aux X d a V (U x) g (f x) hg (hf x), ← hθ x]
  change ((holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op ≫
      (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_left : V ⊓ U x ≤ V)).op) θ =
    ((holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op ≫
      (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE (inf_le_right : V ⊓ U x ≤ U x)).op) θ
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The exterior derivative kills `df`: `d (d f) = 0` on the presheaf, carried through the
sheafification unit. -/
theorem localExactOneForm_differential (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (op U)) :
    (holomorphicDeRhamSheafDifferential X d 1).hom.app (op U) (localExactOneForm X d U f) = 0 := by
  have key : toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d 1) ≫ (holomorphicDeRhamSheafDifferential X d 1).hom =
      holomorphicDeRhamDifferential X d 1 ≫ toSheafify (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (holomorphicDeRhamPresheaf X d (1 + 1)) :=
    (toSheafify_naturality (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamDifferential X d 1)).symm
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app key (op U))
    (Submodule.Quotient.mk (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d (op U)) 0
      (Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d (op U)) f)))
  rw [NatTrans.comp_app, NatTrans.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply] at h
  refine h.trans ?_
  have h0 : (holomorphicDeRhamDifferential X d 1).app (op U)
      (Submodule.Quotient.mk (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d (op U)) 0
      (Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d (op U)) f))) = 0 := by
    change Submodule.Quotient.mk (Algebra.DeRham.differential ℂ _ 1
      (Algebra.DeRham.differential ℂ _ 0 _)) = 0
    rw [Algebra.DeRham.differential_squared]
    exact Submodule.Quotient.mk_zero _
  rw [h0, map_zero]

set_option backward.isDefEq.respectTransparency false in
theorem spec_mem_closedGlobalHolomorphicOneForms_of_locallyExact_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (hθ : ∀ x : ComplexPoint X, ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U)
      (f : OpenHolomorphicFunctions X (dim X.left) (op U)),
        (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.map (homOfLE le_top).op θ =
          localExactOneForm X (dim X.left) U f) :
    θ ∈ closedGlobalHolomorphicOneForms X := by
  choose U hx f hf using hθ
  change (holomorphicDeRhamSheafDifferential X (dim X.left) 1).hom.app (op ⊤) θ = 0
  refine (holomorphicDeRhamSheaf X (dim X.left) (1 + 1)).eq_of_locally_eq' U ⊤
    (fun _ ↦ homOfLE le_top) (fun x _ ↦ Opens.mem_iSup.2 ⟨x, hx x⟩) _ _ fun x ↦ ?_
  rw [map_zero]
  change ((holomorphicDeRhamSheafDifferential X (dim X.left) 1).hom.app (op ⊤) ≫
    (holomorphicDeRhamSheaf X (dim X.left) (1 + 1)).presheaf.map (homOfLE le_top).op) θ = 0
  rw [← (holomorphicDeRhamSheafDifferential X (dim X.left) 1).hom.naturality,
    ConcreteCategory.comp_apply]
  change (holomorphicDeRhamSheafDifferential X (dim X.left) 1).hom.app (op (U x))
    ((holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.map (homOfLE le_top).op θ) = 0
  rw [hf x]
  exact localExactOneForm_differential X _ (U x) (f x)

open scoped Manifold ContDiff in
/-- The extension by zero of a holomorphic function on `U` is holomorphic at the points of `U`. -/
theorem mdifferentiableAt_extendedSection (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (op U)) {x : ComplexPoint X} (hx : x ∈ U) :
    MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) (extendedSection X d (op U) f) x := by
  have h : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω (extendedSection X d (op U) f) x := by
    apply (contMDiffAt_subtype_iff (U := (U : Opens (ComplexPoint X))) (x := ⟨x, hx⟩)).mp
    simpa only [extendedSection, Subtype.val_injective.extend_apply] using
      (holomorphicFunctionSheaf_section_analytic X d f).contMDiffAt (x := ⟨x, hx⟩)
  exact h.mdifferentiableAt (by simp)

open scoped Manifold ContDiff in
/-- The manifold derivative of the extension of `f` at `x ∈ U` is the chart derivative of `f` in
the chart at `x`. -/
theorem mfderiv_extendedSection (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (op U)) {x : ComplexPoint X} (hx : x ∈ U) :
    mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) (extendedSection X d (op U) f) x =
      chartSectionDifferential X d (op U) x f (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) := by
  rw [(mdifferentiableAt_extendedSection X d U f hx).mfderiv, chartSectionDifferential,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d (op U) x)
      (extChartAt_self_mem_chartSectionDomain X d (op U) hx)]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ, Function.id_comp]
  rfl


open scoped Manifold ContDiff in
/-- The value of `θ` at `x` when `θ|_U = df` with `x ∈ U`: the chart derivative of `f` at `x`. -/
theorem globalOneFormCovector_eq_of_localExactOneForm (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (U : Opens (TopCat.of (ComplexPoint X))) (f : OpenHolomorphicFunctions X d (op U))
    (hθ : (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
      localExactOneForm X d U f) {x : ComplexPoint X} (hx : x ∈ U) :
    globalOneFormCovector X d θ x =
      mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) (extendedSection X d (op U) f) x := by
  have hval : globalFormValue X d 1 x θ = chartEvaluation X d (op U) x 1
      (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d (op U)) 0
        (Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d (op U)) f))
      (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) := by
    rw [← spec_formStalkValue_germ_toSheafify X d 1 U x hx]
    change _ = formStalkValue X d x 1 ((holomorphicDeRhamSheaf X d 1).presheaf.germ U x hx
      (localExactOneForm X d U f))
    rw [← hθ]
    change formStalkValue X d x 1 ((holomorphicDeRhamSheaf X d 1).presheaf.germ ⊤ x trivial θ) = _
    rw [TopCat.Presheaf.germ_res_apply]
  rw [mfderiv_extendedSection X d U f hx]
  ext u
  change globalFormValue X d 1 x θ (fun _ ↦ u) = _
  rw [hval, chartEvaluation_differential_ofFunction X d U x f
    (extChartAt_self_mem_chartSectionDomain X d (op U) hx)]

theorem spec_expPullback_eq_of_localExactOneForm_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (a : (Fin d → ℂ) →L[ℂ] ℂ)
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (U : Opens (TopCat.of (ComplexPoint X))) (f : OpenHolomorphicFunctions X d (op U))
    (hf : ∀ v : Fin d → ℂ, (complexExponential X d v).toMul ∈ U →
      HasFDerivAt (fun w ↦ extendedSection X d (op U) f (complexExponential X d w).toMul) a v)
    (hθ : (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
      localExactOneForm X d U f)
    (v : Fin d → ℂ) (hv : (complexExponential X d v).toMul ∈ U) :
    expPullback X d θ v = a := by
  have hcomp := mfderiv_comp v (mdifferentiableAt_extendedSection X d U f hv)
    ((spec_mdifferentiable_complexExponential X d) v)
  rw [mfderiv_eq_fderiv] at hcomp
  ext u
  have h2 := DFunLike.congr_fun hcomp u
  rw [expPullback, globalOneFormCovector_eq_of_localExactOneForm X d θ U f hθ hv,
    ← (hf v hv).fderiv]
  exact h2.symm

theorem spec_exists_closed_expPullback_eq_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (a : (Fin (dim X.left) → ℂ) →L[ℂ] ℂ) :
    ∃ θ ∈ closedGlobalHolomorphicOneForms X, expPullback X (dim X.left) θ 0 = a := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨θ, hθ⟩ := spec_exists_globalForm_of_expPrimitive_aux X (dim X.left) a
  refine ⟨θ, spec_mem_closedGlobalHolomorphicOneForms_of_locallyExact_aux X θ fun x ↦ ?_, ?_⟩
  · obtain ⟨U, hx, f, hf⟩ := spec_exists_local_expPrimitive_aux X (dim X.left) a x
    exact ⟨U, hx, f, hθ U f hf⟩
  · obtain ⟨U, hx, f, hf⟩ := spec_exists_local_expPrimitive_aux X (dim X.left) a
      (complexExponential X (dim X.left) 0).toMul
    exact spec_expPullback_eq_of_localExactOneForm_aux X (dim X.left) a θ U f hf (hθ U f hf) 0 hx

/-- The complexified period map is injective: it factors through the linear equivalence of
`spec_complexAbelianPeriod_restriction` and the injective restriction to the lattice. -/
theorem complexAbelianPeriod_injective (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Function.Injective (complexAbelianPeriod X) := by
  obtain ⟨Φ, hΦ⟩ := spec_complexAbelianPeriod_restriction X
  intro ω ω' h
  rw [← hΦ, ← hΦ] at h
  exact Φ.injective (latticeRestriction_injective X h)

/-- The pullback of the zero form vanishes. -/
theorem expPullback_zero_form (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [GrpObj X] (v : Fin d → ℂ) :
    expPullback X d 0 v = 0 := by
  ext u
  change globalFormValue X d 1 _ 0 (fun _ ↦ _) = 0
  rw [map_zero]
  rfl

theorem spec_exists_periods_ne_zero_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
        bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
          complexAbelianPeriod X ω l = c * ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ),
            expPullback X (dim X.left) (cycleOneForm X z) x := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨c, hsing⟩ := spec_hsing_of_deRham X 1 one_ne_zero fun z Ψ hΨ ↦ by
    rw [one_smul]
    exact spec_deRham_singularIntegrationCochain X z Ψ hΨ
  obtain ⟨s, -, hloop⟩ := spec_periods_of_cohomologyBaseChange X c hsing
  have hper := spec_periods_of_holomorphicPathIntegral X (s * c) hloop
  by_cases h0 : s * c = 0
  · refine ⟨1, one_ne_zero, fun z ω hω l ↦ ?_⟩
    have hω0 : ω = 0 := complexAbelianPeriod_injective X (by
      ext l'
      rw [hper z ω hω l', h0, zero_mul, map_zero, Pi.zero_apply])
    have hz : z = 0 := spec_cycleDeRhamClass_injective_of_isProjective X (by
      rw [← hω, hω0, map_zero, map_zero])
    have hθ : ∀ x, expPullback X (dim X.left) (cycleOneForm X z) x = 0 := fun x ↦ by
      rw [hz, map_zero]
      exact expPullback_zero_form X _ x
    have hint := spec_curveIntegral_segment_expPullback X (dim X.left) (cycleOneForm X z) 0
      (l : Fin (dim X.left) → ℂ)
    rw [hθ, zero_apply] at hint
    rw [hω0, map_zero, Pi.zero_apply]
    erw [hint]
    rw [mul_zero]
  · exact ⟨s * c, h0, hper⟩

/-- A real functional on `ℂ^g` with `f(i v) = i f(v)` is a continuous complex-linear functional. -/
theorem exists_clm_eq_of_mem_degreeOneLatticeHolomorphic {g : ℕ} (f : DegreeOneLatticeDual g)
    (hf : f ∈ degreeOneLatticeHolomorphic g) :
    ∃ a : (Fin g → ℂ) →L[ℂ] ℂ, ∀ v, a v = f v := by
  let a : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun z v ↦ by
        have hz : z • v = z.re • v + z.im • (Complex.I • v) := by
          conv_lhs => rw [← Complex.re_add_im z]
          rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
        rw [hz, map_add, map_smul, map_smul, hf v]
        conv_rhs => rw [← Complex.re_add_im z]
        simp only [Complex.real_smul, RingHom.id_apply]
        ring }
  exact ⟨LinearMap.toContinuousLinearMap a, fun _ ↦ rfl⟩

theorem spec_le_comap_hodgeFiltration_one_of_periods_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c : ℂ) (hc : c ≠ 0)
    (hper : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
        complexAbelianPeriod X ω l = c * ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ),
          expPullback X (dim X.left) (cycleOneForm X z) x) :
    complexHolomorphicH1 X ≤ (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  intro ω hω
  obtain ⟨f, hf, hfω⟩ := hω
  obtain ⟨a, ha⟩ := exists_clm_eq_of_mem_degreeOneLatticeHolomorphic f hf
  obtain ⟨θ, hθ, hθa⟩ := spec_exists_closed_expPullback_eq_aux X (c⁻¹ • a)
  obtain ⟨z, rfl⟩ : θ ∈ (cycleOneForm X).range := by
    rw [spec_range_cycleOneForm X]
    exact hθ
  obtain ⟨ω', hω'⟩ := ((spec_bettiDeRhamIso_abelian X).bijective 1).2 (cycleDeRhamClass X z)
  have heq : ω' = ω := complexAbelianPeriod_injective X (by
    ext l
    have hint := spec_curveIntegral_segment_expPullback X (dim X.left) (cycleOneForm X z) 0
      (l : Fin (dim X.left) → ℂ)
    rw [hθa, sub_zero, smul_apply, ha, smul_eq_mul] at hint
    rw [hper z ω' hω' l, ← hfω]
    erw [hint]
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rfl)
  rw [Submodule.mem_comap, ← heq, hω']
  exact ⟨_, rfl⟩

theorem spec_comap_hodgeFiltration_one_eq_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X := by
  obtain ⟨c, hc, hper⟩ := spec_exists_periods_ne_zero_aux X
  exact le_antisymm (spec_comap_hodgeFiltration_one_le_of_periods X c hper)
    (spec_le_comap_hodgeFiltration_one_of_periods_aux X c hc hper)

theorem spec_le_finrank_hodgeFiltration_one_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    dim X.left ≤ Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) := by
  exact ((spec_comap_hodgeFiltration_one_eq_iff X).mp (spec_comap_hodgeFiltration_one_eq_aux X)).2

theorem spec_deRhamHodgePiece_one_isInternal_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    DirectSum.IsInternal (deRhamHodgePiece X 1) := by
  exact spec_deRhamHodgePiece_one_isInternal_of_comap_eq X (spec_comap_hodgeFiltration_one_eq_aux X)

end HodgeLean.Adapters

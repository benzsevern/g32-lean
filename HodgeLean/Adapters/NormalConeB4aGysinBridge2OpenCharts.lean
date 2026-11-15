import HodgeLean.Adapters.NormalConeB4aClassChartFunction
import HodgeLean.Adapters.NormalConeB4aGysinBridge2DifferentialComparison
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! # Reformulated bridge of A3-B4a: affine opens of fixed dimension and holomorphic readings

A smooth complex scheme has, around every point, an affine open on which it is smooth of a fixed
relative dimension `m`; the local rings at complex points of that open have dimension `m`.
Holomorphic functions on the complex points of a scheme, pulled back along a morphism from a
smooth scheme and read in a holomorphic chart of the source, are analytic. An analytic map with
surjective derivative extends to an analytic chart whose first coordinates are the map.
Source: Hartshorne, *Algebraic Geometry*, Theorem III.10.2; Grauert–Remmert, *Coherent Analytic
Sheaves*, §1.1.5; Dieudonné, *Foundations of Modern Analysis*, (10.2.5). -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry IsLocalRing Point Topology Filter
open HodgeLean.Foundations.Analytic

/-- Affine opens of fixed relative dimension. -/
theorem a3b4g_exists_affine_smoothOfRelativeDimension (X : Over (Spec (CommRingCat.of ℂ)))
    [Smooth X.hom] (x : X.left) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∃ m : ℕ,
      SmoothOfRelativeDimension m (ComplexPoint.openScheme X U).hom := by
  obtain ⟨U, hU, hxU, hs⟩ := Smooth.exists_affine_isStandardSmooth X.hom x
  obtain ⟨d, hd⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension hs
  exact ⟨U, hU, hxU, d, smoothOfRelativeDimension_affineOpen_of_isStandardSmooth X.hom hU hd⟩

/-- The local rings at complex points of an open of fixed relative dimension `m` have dimension
`m`. -/
theorem a3b4g_ringKrullDim_stalk_of_openScheme (X : Over (Spec (CommRingCat.of ℂ)))
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) {m : ℕ}
    [SmoothOfRelativeDimension m (ComplexPoint.openScheme X U).hom]
    (z : ComplexPoint X) (hz : z ∈ overOpen U) :
    ringKrullDim (X.left.presheaf.stalk z.underlying) = m := by
  let Y := ComplexPoint.openScheme X U
  letI : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  let zU := ComplexPoint.asOpenPoint X U z hz
  have hfz : Point.map (ComplexPoint.openInclusion X U) zU = z :=
    Over.OverMorphism.ext (ComplexPoint.liftToOpen_fac X U z hz)
  have hdim := a3b4g_ringKrullDim_stalk_of_smooth Y (d := m) zU.underlying
    (a3b4g_isClosed_underlying Y zU)
  have hu : U.ι zU.underlying = z.underlying := by
    rw [← hfz]
    rfl
  let e : X.left.presheaf.stalk (U.ι zU.underlying) ≃+* Y.left.presheaf.stalk zU.underlying :=
    (asIso (U.ι.stalkMap zU.underlying)).commRingCatIsoToRingEquiv
  have key : ∀ p (_ : U.ι zU.underlying = p), ringKrullDim (X.left.presheaf.stalk p) = m := by
    rintro p rfl
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact hdim
  exact key _ hu

/-- Holomorphic functions pulled back along a morphism from a smooth scheme are analytic in a
holomorphic chart of the source. -/
theorem a3b4g_holFun_comp_chart_analytic (X Y : Over (Spec (CommRingCat.of ℂ))) [Smooth X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
    {r c : ℕ} (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (V : Set (ComplexPoint Y)) (hV : IsOpen V)
    (g : ComplexPoint Y → ℂ) (hg : (f4_analytification Y).IsHolFun (fun z : V => g z))
    (v : (Fin r → ℂ) × (Fin c → ℂ)) (hv : v ∈ e.target) (hvV : Point.map f (e.symm v) ∈ V) :
    AnalyticAt ℂ (fun v => g (Point.map f (e.symm v))) v := by
  have hW : IsOpen (Point.map f ⁻¹' V) := hV.preimage (Point.continuous_map f)
  have hg' := (f4_map_isHom f).2 V hV (fun z : V => g z) hg
  exact a3b4a_classHolomorphicChart_function_analytic X e he _ hW (fun x => g (Point.map f x))
    hg' v hv hvV

/-- Regular functions pulled back along a morphism from a smooth scheme are analytic in a
holomorphic chart of the source. -/
theorem a3b4g_evaluate_comp_chart_analytic (X Y : Over (Spec (CommRingCat.of ℂ))) [Smooth X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
    {r c : ℕ} (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (W : Y.left.Opens) (σ : Γ(Y.left, W))
    (v : (Fin r → ℂ) × (Fin c → ℂ)) (hv : v ∈ e.target)
    (hvW : Point.map f (e.symm v) ∈ overOpen (X := Y) W) :
    AnalyticAt ℂ (fun v => evaluate W σ (Point.map f (e.symm v))) v :=
  a3b4g_holFun_comp_chart_analytic X Y f e he _ (isOpen_overOpen W) (fun z => evaluate W σ z)
    (f4_isHolFun_evaluate Y W σ) v hv hvW

/-- An analytic map with a right-inverted derivative is the first coordinate of an analytic
chart. -/
theorem a3b4g_analytic_splitSubmersion_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {g : E → F} {a : E} (hg : AnalyticAt ℂ g a)
    (B : F →L[ℂ] E)
    (hAB : (fderiv ℂ g a).comp B = ContinuousLinearMap.id ℂ F) :
    ∃ e : OpenPartialHomeomorph E (F × (fderiv ℂ g a).ker),
      a ∈ e.source ∧ (∀ y : E, (e y).1 = g y) ∧
      AnalyticAt ℂ e a ∧ AnalyticAt ℂ e.symm (e a) ∧
      ∃ L : E ≃L[ℂ] F × (fderiv ℂ g a).ker, HasStrictFDerivAt e (L : E →L[ℂ] _) a := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let A := fderiv ℂ g a
  let L := (B.splitKernelEquiv A hAB).symm
  let K : E →L[ℂ] A.ker :=
    (ContinuousLinearMap.snd ℂ F A.ker).comp L.toContinuousLinearMap
  have hd : HasStrictFDerivAt (fun y => (g y, K y)) L.toContinuousLinearMap a := by
    convert hg.hasStrictFDerivAt.prodMk K.hasStrictFDerivAt using 1
    ext y <;> rfl
  let e := hd.toOpenPartialHomeomorph _
  have ha : a ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  have heA : AnalyticAt ℂ e a := hg.prod (K.analyticAt a)
  have heI : AnalyticAt ℂ e.symm (e a) :=
    e.analyticAt_symm' ha heA hd.hasFDerivAt.fderiv
  exact ⟨e, ha, fun _ => rfl, heA, heI, L, hd⟩

end HodgeLean.Adapters

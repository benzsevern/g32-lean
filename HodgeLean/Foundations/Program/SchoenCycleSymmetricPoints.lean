import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap
import HodgeLean.Foundations.SegreProjectiveProofs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeLean.Foundations.Program.SchoenCycleGeometryChecks
import HodgeLean.Foundations.Program.SchoenCycleTupleMultiplicity

/-! # Points of the retained symmetric quotient
Coordinate permutations do not change the image of a tuple in the retained quotient.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Morphisms to the retained scheme power are determined by their coordinates. -/
theorem s2e_power_hom_ext {T Y : Over (Spec ↧ℂ)} (n : ℕ)
    (f g : T ⟶ g3_power Y n)
    (h : ∀ i, f ≫ g3_proj Y n i = g ≫ g3_proj Y n i) : f = g := by
  induction n with
  | zero => exact (SemiCartesianMonoidalCategory.isTerminalTensorUnit).hom_ext f g
  | succ n ih =>
    apply CartesianMonoidalCategory.hom_ext f g
    · exact h 0
    · apply ih
      intro i
      have hi := h i.succ
      change f ≫ (CartesianMonoidalCategory.snd Y (g3_power Y n) ≫ g3_proj Y n i) =
        g ≫ (CartesianMonoidalCategory.snd Y (g3_power Y n) ≫ g3_proj Y n i) at hi
      simpa only [Category.assoc] using hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A coordinate permutation of a lifted tuple is the lift of the reordered tuple. -/
theorem s2e_lift_permute {T Y : Over (Spec ↧ℂ)} (n : ℕ)
    (f : Fin n → (T ⟶ Y)) (σ : Equiv.Perm (Fin n)) :
    s2_lift n f ≫ s2_permute Y n σ = s2_lift n (fun i => f (σ.symm i)) := by
  apply s2e_power_hom_ext
  intro i
  simp only [Category.assoc, s2_permute, s2_check_lift_proj]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reordering a tuple leaves its image under the retained quotient unchanged. -/
theorem s2e_quotient_tuple_permutation {T Y B : Over (Spec ↧ℂ)} (n : ℕ)
    (γ : g3_power Y n ⟶ B) (hγ : ∀ σ, s2_permute Y n σ ≫ γ = γ)
    (f : Fin n → (T ⟶ Y)) (σ : Equiv.Perm (Fin n)) :
    s2_lift n (fun i => f (σ i)) ≫ γ = s2_lift n f ≫ γ := by
  have hp := s2e_lift_permute n f σ.symm
  simp only [Equiv.symm_symm] at hp
  rw [← hp, Category.assoc, hγ]

/-- Equal unordered tuples have the same image in the retained symmetric quotient. -/
theorem s2e_quotient_tuple_multiset_eq {T Y B : Over (Spec ↧ℂ)} (n : ℕ)
    (γ : g3_power Y n ⟶ B) (hγ : ∀ σ, s2_permute Y n σ ≫ γ = γ)
    (f g : Fin n → (T ⟶ Y))
    (h : (List.ofFn f : Multiset (T ⟶ Y)) = List.ofFn g) :
    s2_lift n f ≫ γ = s2_lift n g ≫ γ := by
  obtain ⟨σ, hσ⟩ := s2e_tuple_permutation_of_multiset_eq f g h
  have hf : f = fun i => g (σ i) := funext (fun i => (hσ i).symm)
  rw [hf]
  exact s2e_quotient_tuple_permutation n γ hγ g σ

/-- Evaluate an unordered tuple of generalized points in the retained quotient.
Source: Schoen (1988), §2, p. 12; Mac Lane, Categories for the Working Mathematician, III.4. -/
def s2e_symmetricQuotientEvaluation {T Y B : Over (Spec ↧ℂ)} (n : ℕ)
    (γ : g3_power Y n ⟶ B) (s : Sym (T ⟶ Y) n) : T ⟶ B :=
  s2_lift n (s2e_symEnumeration s) ≫ γ

example {T Y B : Over (Spec ↧ℂ)} (n : ℕ)
    (γ : g3_power Y n ⟶ B) (s : Sym (T ⟶ Y) n) :
    s2e_symmetricQuotientEvaluation n γ s = s2_lift n (s2e_symEnumeration s) ≫ γ := rfl

/-- The quotient evaluation agrees with every enumeration, independently of the choice. -/
theorem s2e_symmetricQuotientEvaluation_eq {T Y B : Over (Spec ↧ℂ)} (n : ℕ)
    (γ : g3_power Y n ⟶ B) (hγ : ∀ σ, s2_permute Y n σ ≫ γ = γ)
    (s : Sym (T ⟶ Y) n) (f : Fin n → (T ⟶ Y))
    (hf : (List.ofFn f : Multiset (T ⟶ Y)) = s) :
    s2e_symmetricQuotientEvaluation n γ s = s2_lift n f ≫ γ := by
  apply s2e_quotient_tuple_multiset_eq n γ hγ
  exact (s2e_sym_exists_enumeration s).choose_spec.trans hf.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism into a tuple acts by precomposition in every coordinate. -/
theorem s2e_comp_lift {T U Y : Over (Spec ↧ℂ)} (n : ℕ)
    (u : T ⟶ U) (f : Fin n → (U ⟶ Y)) :
    u ≫ s2_lift n f = s2_lift n (fun i => u ≫ f i) := by
  apply s2e_power_hom_ext
  intro i
  simp only [Category.assoc, s2_check_lift_proj]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Unordered quotient evaluation is natural in the scheme of generalized points. -/
theorem s2e_symmetricQuotientEvaluation_precomp {T U Y B : Over (Spec ↧ℂ)} (n : ℕ)
    (γ : g3_power Y n ⟶ B) (hγ : ∀ σ, s2_permute Y n σ ≫ γ = γ)
    (u : T ⟶ U) (s : Sym (U ⟶ Y) n) :
    s2e_symmetricQuotientEvaluation n γ (s.map (fun f => u ≫ f)) =
      u ≫ s2e_symmetricQuotientEvaluation n γ s := by
  rw [s2e_symmetricQuotientEvaluation_eq n γ hγ _
    (fun i => u ≫ s2e_symEnumeration s i)
    (s2e_sym_map_enumeration s _ (s2e_sym_exists_enumeration s).choose_spec _)]
  change s2_lift n (fun i => u ≫ s2e_symEnumeration s i) ≫ γ =
    u ≫ (s2_lift n (s2e_symEnumeration s) ≫ γ)
  rw [← s2e_comp_lift, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The retained scheme power recovers every generalized point from its coordinates. -/
theorem s2e_lift_coordinates {T Y : Over (Spec ↧ℂ)} (n : ℕ) (z : T ⟶ g3_power Y n) :
    s2_lift n (fun i => z ≫ g3_proj Y n i) = z := by
  apply s2e_power_hom_ext
  intro i
  exact s2_check_lift_proj n _ i

/-- Surjectivity of the retained quotient on complex points gives surjective unordered evaluation. -/
theorem s2e_symmetricQuotientEvaluation_surjective {Y B : Over (Spec ↧ℂ)} (n : ℕ)
    (γ : g3_power Y n ⟶ B) (hγ : ∀ σ, s2_permute Y n σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ)) :
    Function.Surjective (s2e_symmetricQuotientEvaluation n γ :
      Sym (ComplexPoint Y) n → ComplexPoint B) := by
  intro b
  obtain ⟨z, hz⟩ := hsurj b
  let f : Fin n → ComplexPoint Y := fun i => z ≫ g3_proj Y n i
  let s : Sym (ComplexPoint Y) n := ⟨List.ofFn f, by simp⟩
  refine ⟨s, ?_⟩
  rw [s2e_symmetricQuotientEvaluation_eq n γ hγ s f rfl]
  change s2_lift n (fun i => z ≫ g3_proj Y n i) ≫ γ = b
  rw [s2e_lift_coordinates]
  exact hz

/-- Generalized points of the retained scheme power are exactly tuples of generalized points. -/
def s2e_powerPointEquiv (T Y : Over (Spec ↧ℂ)) (n : ℕ) :
    (T ⟶ g3_power Y n) ≃ (Fin n → (T ⟶ Y)) where
  toFun z i := z ≫ g3_proj Y n i
  invFun := s2_lift n
  left_inv := s2e_lift_coordinates n
  right_inv f := by
    funext i
    exact s2_check_lift_proj n f i

/-- Coordinates of native complex scheme-power points vary continuously. -/
theorem s2e_powerPoint_coordinates_continuous (Y : Over (Spec ↧ℂ)) (n : ℕ) :
    Continuous (fun z : ComplexPoint (g3_power Y n) =>
      fun i : Fin n => Point.map (g3_proj Y n i) z) := by
  exact continuous_pi fun i => Point.continuous_map (g3_proj Y n i)

/-- For compact native power points and Hausdorff curve points, the tuple comparison is a homeomorphism. -/
def s2e_powerPointHomeomorph (Y : Over (Spec ↧ℂ)) (n : ℕ)
    [CompactSpace (ComplexPoint (g3_power Y n))] [T2Space (ComplexPoint Y)] :
    ComplexPoint (g3_power Y n) ≃ₜ (Fin n → ComplexPoint Y) :=
  (show ComplexPoint (g3_power Y n) ≃ (Fin n → ComplexPoint Y) from
    { toFun := fun z i => Point.map (g3_proj Y n i) z
      invFun := s2_lift n
      left_inv := s2e_lift_coordinates n
      right_inv := fun f => funext (fun i => s2_check_lift_proj n f i) }).toHomeomorphOfContinuousClosed
    (s2e_powerPoint_coordinates_continuous Y n)
    (s2e_powerPoint_coordinates_continuous Y n).isClosedMap

/-- Projectivity supplies the topological hypotheses for the native power-point comparison. -/
def s2e_projectivePowerPointHomeomorph (Y : Over (Spec ↧ℂ))
    [IsProjective Y.hom] (n : ℕ) :
    ComplexPoint (g3_power Y n) ≃ₜ (Fin n → ComplexPoint Y) :=
  s2e_powerPointHomeomorph Y n

/-- Each retained power projection is analytic in the native algebraic coordinate charts. -/
theorem s2e_power_projection_chart_analytic
    (Y : Over (Spec ↧ℂ)) (n d e : ℕ)
    [SmoothOfRelativeDimension d (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (i : Fin n) (z : ComplexPoint (g3_power Y n)) {w : Fin d → ℂ}
    (hw : w ∈ (localChart (g3_power Y n) d z).target)
    (hmap : Point.map (g3_proj Y n i) ((localChart (g3_power Y n) d z).symm w) ∈
      (localChart Y e (Point.map (g3_proj Y n i) z)).source) :
    AnalyticAt ℂ (fun v => localChart Y e (Point.map (g3_proj Y n i) z)
      (Point.map (g3_proj Y n i) ((localChart (g3_power Y n) d z).symm v))) w :=
  analyticAt_localChart_symm_map (g3_power Y n) Y (g3_proj Y n i) d e z hw hmap

/-- The tuple of retained projections is jointly analytic in native coordinate charts. -/
theorem s2e_power_coordinates_chart_analytic
    (Y : Over (Spec ↧ℂ)) (n d e : ℕ)
    [SmoothOfRelativeDimension d (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) {w : Fin d → ℂ}
    (hw : w ∈ (localChart (g3_power Y n) d z).target)
    (hmap : ∀ i : Fin n,
      Point.map (g3_proj Y n i) ((localChart (g3_power Y n) d z).symm w) ∈
        (localChart Y e (Point.map (g3_proj Y n i) z)).source) :
    AnalyticAt ℂ (fun v => fun i : Fin n =>
      localChart Y e (Point.map (g3_proj Y n i) z)
        (Point.map (g3_proj Y n i) ((localChart (g3_power Y n) d z).symm v))) w := by
  exact AnalyticAt.pi fun i => s2e_power_projection_chart_analytic Y n d e i z hw (hmap i)

/-- Native tuple coordinates are analytic at the chart centre without extra membership premises. -/
theorem s2e_power_coordinates_chart_analytic_at_center
    (Y : Over (Spec ↧ℂ)) (n d e : ℕ)
    [SmoothOfRelativeDimension d (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) :
    AnalyticAt ℂ (fun v => fun i : Fin n =>
      localChart Y e (Point.map (g3_proj Y n i) z)
        (Point.map (g3_proj Y n i) ((localChart (g3_power Y n) d z).symm v)))
      (localChart (g3_power Y n) d z z) := by
  have hz := mem_localChart_source (g3_power Y n) d z
  apply s2e_power_coordinates_chart_analytic Y n d e z
  · exact (localChart (g3_power Y n) d z).map_source hz
  · intro i
    rw [(localChart (g3_power Y n) d z).left_inv hz]
    exact mem_localChart_source Y e _

/-- Native power coordinates distinguish points in a common family of curve charts. -/
theorem s2e_power_chart_coordinates_injective
    (Y : Over (Spec ↧ℂ)) (n e : ℕ) [SmoothOfRelativeDimension e Y.hom]
    (z x y : ComplexPoint (g3_power Y n))
    (hx : ∀ i : Fin n, Point.map (g3_proj Y n i) x ∈
      (localChart Y e (Point.map (g3_proj Y n i) z)).source)
    (hy : ∀ i : Fin n, Point.map (g3_proj Y n i) y ∈
      (localChart Y e (Point.map (g3_proj Y n i) z)).source)
    (h : ∀ i : Fin n,
      localChart Y e (Point.map (g3_proj Y n i) z) (Point.map (g3_proj Y n i) x) =
      localChart Y e (Point.map (g3_proj Y n i) z) (Point.map (g3_proj Y n i) y)) : x = y := by
  apply s2e_power_hom_ext
  intro i
  exact (localChart Y e (Point.map (g3_proj Y n i) z)).injOn (hx i) (hy i) (h i)

/-- The common curve-chart domain is an open neighbourhood of a native power point. -/
theorem s2e_power_common_chart_neighbourhood
    (Y : Over (Spec ↧ℂ)) (n e : ℕ) [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) :
    IsOpen {x : ComplexPoint (g3_power Y n) | ∀ i : Fin n,
      Point.map (g3_proj Y n i) x ∈
        (localChart Y e (Point.map (g3_proj Y n i) z)).source} ∧
      z ∈ {x : ComplexPoint (g3_power Y n) | ∀ i : Fin n,
        Point.map (g3_proj Y n i) x ∈
          (localChart Y e (Point.map (g3_proj Y n i) z)).source} := by
  constructor
  · have h := isOpen_iInter_of_finite fun i : Fin n =>
      (localChart Y e (Point.map (g3_proj Y n i) z)).open_source.preimage
        (Point.continuous_map (g3_proj Y n i))
    convert h using 1
    ext x
    simp
  · intro i
    exact mem_localChart_source Y e _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every tuple in the target charts is reconstructed by an actual native power point. -/
theorem s2e_power_chart_tuple_reconstruction
    (Y : Over (Spec ↧ℂ)) (n e : ℕ) [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) (v : Fin n → Fin e → ℂ)
    (hv : ∀ i, v i ∈ (localChart Y e (Point.map (g3_proj Y n i) z)).target) :
    ∃ x : ComplexPoint (g3_power Y n),
      (∀ i, Point.map (g3_proj Y n i) x ∈
        (localChart Y e (Point.map (g3_proj Y n i) z)).source) ∧
      ∀ i, localChart Y e (Point.map (g3_proj Y n i) z)
        (Point.map (g3_proj Y n i) x) = v i := by
  let f (i : Fin n) : ComplexPoint Y :=
    (localChart Y e (Point.map (g3_proj Y n i) z)).symm (v i)
  refine ⟨s2_lift n f, ?_, ?_⟩
  · intro i
    change (s2_lift n f ≫ g3_proj Y n i) ∈ _
    rw [s2_check_lift_proj]
    exact (localChart Y e (Point.map (g3_proj Y n i) z)).map_target (hv i)
  · intro i
    change localChart Y e (Point.map (g3_proj Y n i) z)
      (s2_lift n f ≫ g3_proj Y n i) = v i
    rw [s2_check_lift_proj]
    exact (localChart Y e (Point.map (g3_proj Y n i) z)).right_inv (hv i)

/-- A tuple in the curve-chart targets has a unique native preimage in the common chart domain. -/
theorem s2e_power_chart_tuple_unique
    (Y : Over (Spec ↧ℂ)) (n e : ℕ) [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) (v : Fin n → Fin e → ℂ)
    (hv : ∀ i, v i ∈ (localChart Y e (Point.map (g3_proj Y n i) z)).target) :
    ∃! x : ComplexPoint (g3_power Y n),
      (∀ i, Point.map (g3_proj Y n i) x ∈
        (localChart Y e (Point.map (g3_proj Y n i) z)).source) ∧
      ∀ i, localChart Y e (Point.map (g3_proj Y n i) z)
        (Point.map (g3_proj Y n i) x) = v i := by
  obtain ⟨x, hx, hcoords⟩ := s2e_power_chart_tuple_reconstruction Y n e z v hv
  refine ⟨x, ⟨hx, hcoords⟩, ?_⟩
  intro y hy
  apply s2e_power_chart_coordinates_injective Y n e z y x hy.1 hx
  intro i
  exact (hy.2 i).trans (hcoords i).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Native points in the common chart domain are equivalent to tuples in the chart targets. -/
def s2e_powerChartDomainEquiv
    (Y : Over (Spec ↧ℂ)) (n e : ℕ) [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) :
    {x : ComplexPoint (g3_power Y n) // ∀ i : Fin n,
      Point.map (g3_proj Y n i) x ∈ (localChart Y e (Point.map (g3_proj Y n i) z)).source} ≃
    {v : Fin n → Fin e → ℂ // ∀ i,
      v i ∈ (localChart Y e (Point.map (g3_proj Y n i) z)).target} where
  toFun x := ⟨fun i => localChart Y e (Point.map (g3_proj Y n i) z)
    (Point.map (g3_proj Y n i) x.val),
    fun i => (localChart Y e (Point.map (g3_proj Y n i) z)).map_source (x.property i)⟩
  invFun v := ⟨(s2e_power_chart_tuple_reconstruction Y n e z v.val v.property).choose,
    (s2e_power_chart_tuple_reconstruction Y n e z v.val v.property).choose_spec.1⟩
  left_inv x := by
    let v : Fin n → Fin e → ℂ := fun i =>
      localChart Y e (Point.map (g3_proj Y n i) z) (Point.map (g3_proj Y n i) x.val)
    have hv : ∀ i, v i ∈ (localChart Y e (Point.map (g3_proj Y n i) z)).target :=
      fun i => (localChart Y e (Point.map (g3_proj Y n i) z)).map_source (x.property i)
    apply Subtype.ext
    exact s2e_power_chart_coordinates_injective Y n e z _ x.val
      (s2e_power_chart_tuple_reconstruction Y n e z v hv).choose_spec.1 x.property
      (s2e_power_chart_tuple_reconstruction Y n e z v hv).choose_spec.2
  right_inv v := by
    apply Subtype.ext
    funext i
    exact (s2e_power_chart_tuple_reconstruction Y n e z v.val v.property).choose_spec.2 i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse chart-domain equivalence has the prescribed inverse-chart projection coordinates. -/
theorem s2e_powerChartDomainEquiv_symm_projection
    (Y : Over (Spec ↧ℂ)) (n e : ℕ) [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n))
    (v : {v : Fin n → Fin e → ℂ // ∀ i,
      v i ∈ (localChart Y e (Point.map (g3_proj Y n i) z)).target}) (i : Fin n) :
    Point.map (g3_proj Y n i) ((s2e_powerChartDomainEquiv Y n e z).symm v).val =
      (localChart Y e (Point.map (g3_proj Y n i) z)).symm (v.val i) := by
  have hs := (s2e_power_chart_tuple_reconstruction Y n e z v.val v.property).choose_spec
  change Point.map (g3_proj Y n i)
    (s2e_power_chart_tuple_reconstruction Y n e z v.val v.property).choose = _
  exact ((localChart Y e (Point.map (g3_proj Y n i) z)).left_inv (hs.1 i)).symm.trans
    (congrArg (localChart Y e (Point.map (g3_proj Y n i) z)).symm (hs.2 i))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse chart-domain equivalence is exactly the retained lift of inverse-chart points. -/
theorem s2e_powerChartDomainEquiv_symm_eq_lift
    (Y : Over (Spec ↧ℂ)) (n e : ℕ) [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n))
    (v : {v : Fin n → Fin e → ℂ // ∀ i,
      v i ∈ (localChart Y e (Point.map (g3_proj Y n i) z)).target}) :
    ((s2e_powerChartDomainEquiv Y n e z).symm v).val =
      s2_lift n (fun i => (localChart Y e (Point.map (g3_proj Y n i) z)).symm (v.val i)) := by
  apply s2e_power_hom_ext
  intro i
  rw [s2_check_lift_proj]
  exact s2e_powerChartDomainEquiv_symm_projection Y n e z v i

/-- The retained tuple lift is continuous for projective complex schemes. -/
theorem s2e_projective_tuple_lift_continuous
    (Y : Over (Spec ↧ℂ)) [IsProjective Y.hom] (n : ℕ) :
    Continuous (s2_lift n : (Fin n → ComplexPoint Y) → ComplexPoint (g3_power Y n)) := by
  exact (s2e_projectivePowerPointHomeomorph Y n).symm.continuous

/-- For projective schemes, reconstruction from curve-chart targets is continuous. -/
theorem s2e_powerChartDomainEquiv_symm_continuous
    (Y : Over (Spec ↧ℂ)) [IsProjective Y.hom] (n e : ℕ)
    [SmoothOfRelativeDimension e Y.hom] (z : ComplexPoint (g3_power Y n)) :
    Continuous (s2e_powerChartDomainEquiv Y n e z).symm := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun v : {v : Fin n → Fin e → ℂ // ∀ i,
      v i ∈ (localChart Y e (Point.map (g3_proj Y n i) z)).target} =>
      fun i => (localChart Y e (Point.map (g3_proj Y n i) z)).symm (v.val i)) := by
    apply continuous_pi
    intro i
    apply (localChart Y e (Point.map (g3_proj Y n i) z)).continuousOn_symm.comp_continuous
      ((continuous_apply i).comp continuous_subtype_val)
    intro v
    exact v.property i
  have hh := (s2e_projective_tuple_lift_continuous Y n).comp hc
  exact hh.congr (fun v => (s2e_powerChartDomainEquiv_symm_eq_lift Y n e z v).symm)

/-- The forward chart-domain equivalence is continuous on the common native chart domain. -/
theorem s2e_powerChartDomainEquiv_continuous
    (Y : Over (Spec ↧ℂ)) (n e : ℕ) [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) :
    Continuous (s2e_powerChartDomainEquiv Y n e z) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply (localChart Y e (Point.map (g3_proj Y n i) z)).continuousOn.comp_continuous
    ((Point.continuous_map (g3_proj Y n i)).comp continuous_subtype_val)
  intro x
  exact x.property i

/-- For projective schemes the common native chart domain is homeomorphic to the tuple chart targets. -/
def s2e_powerChartDomainHomeomorph
    (Y : Over (Spec ↧ℂ)) [IsProjective Y.hom] (n e : ℕ)
    [SmoothOfRelativeDimension e Y.hom] (z : ComplexPoint (g3_power Y n)) :
    {x : ComplexPoint (g3_power Y n) // ∀ i : Fin n,
      Point.map (g3_proj Y n i) x ∈ (localChart Y e (Point.map (g3_proj Y n i) z)).source} ≃ₜ
    {v : Fin n → Fin e → ℂ // ∀ i,
      v i ∈ (localChart Y e (Point.map (g3_proj Y n i) z)).target} where
  toEquiv := s2e_powerChartDomainEquiv Y n e z
  continuous_toFun := s2e_powerChartDomainEquiv_continuous Y n e z
  continuous_invFun := s2e_powerChartDomainEquiv_symm_continuous Y n e z

/-- The native tuple chart map has its strict complex derivative at the chart centre. -/
theorem s2e_power_coordinates_chart_hasStrictFDerivAt
    (Y : Over (Spec ↧ℂ)) (n d e : ℕ)
    [SmoothOfRelativeDimension d (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) :
    let F := fun v => fun i : Fin n =>
      localChart Y e (Point.map (g3_proj Y n i) z)
        (Point.map (g3_proj Y n i) ((localChart (g3_power Y n) d z).symm v))
    HasStrictFDerivAt F (fderiv ℂ F (localChart (g3_power Y n) d z z))
      (localChart (g3_power Y n) d z z) := by
  exact (s2e_power_coordinates_chart_analytic_at_center Y n d e z).hasStrictFDerivAt

/-- Equality of tuple coordinates in native power charts forces equality of chart parameters. -/
theorem s2e_power_coordinates_chart_injective
    (Y : Over (Spec ↧ℂ)) (n d e : ℕ)
    [SmoothOfRelativeDimension d (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) (u v : Fin d → ℂ)
    (hu : u ∈ (localChart (g3_power Y n) d z).target)
    (hv : v ∈ (localChart (g3_power Y n) d z).target)
    (hus : ∀ i, Point.map (g3_proj Y n i) ((localChart (g3_power Y n) d z).symm u) ∈
      (localChart Y e (Point.map (g3_proj Y n i) z)).source)
    (hvs : ∀ i, Point.map (g3_proj Y n i) ((localChart (g3_power Y n) d z).symm v) ∈
      (localChart Y e (Point.map (g3_proj Y n i) z)).source)
    (h : ∀ i, localChart Y e (Point.map (g3_proj Y n i) z)
      (Point.map (g3_proj Y n i) ((localChart (g3_power Y n) d z).symm u)) =
      localChart Y e (Point.map (g3_proj Y n i) z)
      (Point.map (g3_proj Y n i) ((localChart (g3_power Y n) d z).symm v))) : u = v := by
  have he := s2e_power_chart_coordinates_injective Y n e z _ _ hus hvs h
  exact (localChart (g3_power Y n) d z).symm.injOn hu hv he

/-- Vary one factor of the retained power and keep the other factors at the given point. -/
def s2e_powerFactorSection (Y : Over (Spec ↧ℂ)) (n : ℕ)
    (z : ComplexPoint (g3_power Y n)) (i : Fin n) : Y ⟶ g3_power Y n :=
  s2_lift n (fun j => if j = i then 𝟙 Y else
    Over.mkIdTerminal.from Y ≫ (z ≫ g3_proj Y n j))

/-- A factor section changes precisely its selected coordinate on native points. -/
theorem s2e_powerFactorSection_projection (Y : Over (Spec ↧ℂ)) (n : ℕ)
    (z : ComplexPoint (g3_power Y n)) (i j : Fin n) (x : ComplexPoint Y) :
    Point.map (g3_proj Y n j) (Point.map (s2e_powerFactorSection Y n z i) x) =
      if j = i then x else Point.map (g3_proj Y n j) z := by
  change x ≫ s2e_powerFactorSection Y n z i ≫ g3_proj Y n j = _
  rw [s2e_powerFactorSection, s2_check_lift_proj]
  split_ifs with h
  · simp
  · have ht : x ≫ Over.mkIdTerminal.from Y = 𝟙 _ := Over.mkIdTerminal.hom_ext _ _
    rw [← Category.assoc, ht, Category.id_comp]
    rfl

/-- The selected base coordinate maps back to the original native power point. -/
theorem s2e_powerFactorSection_base (Y : Over (Spec ↧ℂ)) (n : ℕ)
    (z : ComplexPoint (g3_power Y n)) (i : Fin n) :
    Point.map (s2e_powerFactorSection Y n z i) (Point.map (g3_proj Y n i) z) = z := by
  apply s2e_power_hom_ext
  intro j
  change Point.map (g3_proj Y n j)
    (Point.map (s2e_powerFactorSection Y n z i) (Point.map (g3_proj Y n i) z)) = _
  rw [s2e_powerFactorSection_projection]
  split_ifs with h
  · subst j; rfl
  · rfl

/-- Each factor section is analytic in native charts through the retained base point. -/
theorem s2e_powerFactorSection_chart_analytic
    (Y : Over (Spec ↧ℂ)) (n d e : ℕ)
    [SmoothOfRelativeDimension d (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) (i : Fin n) :
    AnalyticAt ℂ (fun v => localChart (g3_power Y n) d z
      (Point.map (s2e_powerFactorSection Y n z i)
        ((localChart Y e (Point.map (g3_proj Y n i) z)).symm v)))
      (localChart Y e (Point.map (g3_proj Y n i) z) (Point.map (g3_proj Y n i) z)) := by
  have hx := mem_localChart_source Y e (Point.map (g3_proj Y n i) z)
  have ha := analyticAt_localChart_symm_map Y (g3_power Y n)
    (s2e_powerFactorSection Y n z i) e d (Point.map (g3_proj Y n i) z)
    ((localChart Y e _).map_source hx)
  rw [s2e_powerFactorSection_base] at ha
  apply ha
  rw [(localChart Y e _).left_inv hx, s2e_powerFactorSection_base]
  exact mem_localChart_source (g3_power Y n) d z

/-- Composing a native factor section with tuple coordinates locally replaces one block. -/
theorem s2e_powerFactorSection_chart_coordinates
    (Y : Over (Spec ↧ℂ)) (n d e : ℕ)
    [SmoothOfRelativeDimension d (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) (i : Fin n) :
    let C := localChart (g3_power Y n) d z
    let c := fun j => localChart Y e (Point.map (g3_proj Y n j) z)
    let a := fun j => c j (Point.map (g3_proj Y n j) z)
    let G := fun v => C (Point.map (s2e_powerFactorSection Y n z i) ((c i).symm v))
    let F := fun v => fun j => c j (Point.map (g3_proj Y n j) (C.symm v))
    ∀ᶠ v in nhds (a i), F (G v) = Function.update a i v := by
  dsimp only
  let C := localChart (g3_power Y n) d z
  let c := localChart Y e (Point.map (g3_proj Y n i) z)
  have hx := mem_localChart_source Y e (Point.map (g3_proj Y n i) z)
  have ht : c (Point.map (g3_proj Y n i) z) ∈ c.target := c.map_source hx
  have hc := (Point.continuous_map (s2e_powerFactorSection Y n z i)).continuousAt.comp
    (c.continuousAt_symm ht)
  have hb : Point.map (s2e_powerFactorSection Y n z i)
      (c.symm (c (Point.map (g3_proj Y n i) z))) = z := by
    rw [c.left_inv hx, s2e_powerFactorSection_base]
  have hs : ∀ᶠ v in nhds (c (Point.map (g3_proj Y n i) z)),
      Point.map (s2e_powerFactorSection Y n z i) (c.symm v) ∈ C.source := by
    apply hc
    dsimp only [Function.comp_def]
    rw [hb]
    exact C.open_source.mem_nhds (mem_localChart_source (g3_power Y n) d z)
  filter_upwards [hs, c.open_target.mem_nhds ht] with v hv hvt
  funext j
  rw [C.left_inv hv, s2e_powerFactorSection_projection]
  by_cases hji : j = i
  · subst j
    simp only [ite_true, Function.update_self]
    exact c.right_inv hvt
  · simp only [hji, ite_false, Function.update_of_ne hji]

/-- Differentiating a factor section gives a right inverse on its tuple-coordinate block. -/
theorem s2e_powerFactorSection_chart_fderiv
    (Y : Over (Spec ↧ℂ)) (n d e : ℕ)
    [SmoothOfRelativeDimension d (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) (i : Fin n) :
    let C := localChart (g3_power Y n) d z
    let c := fun j => localChart Y e (Point.map (g3_proj Y n j) z)
    let a := fun j => c j (Point.map (g3_proj Y n j) z)
    let G := fun v => C (Point.map (s2e_powerFactorSection Y n z i) ((c i).symm v))
    let F := fun v => fun j => c j (Point.map (g3_proj Y n j) (C.symm v))
    (fderiv ℂ F (C z)).comp (fderiv ℂ G (a i)) =
      ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℂ (Fin e → ℂ))) := by
  dsimp only
  let C := localChart (g3_power Y n) d z
  let c := fun j => localChart Y e (Point.map (g3_proj Y n j) z)
  let a := fun j => c j (Point.map (g3_proj Y n j) z)
  let G := fun v => C (Point.map (s2e_powerFactorSection Y n z i) ((c i).symm v))
  let F := fun v => fun j => c j (Point.map (g3_proj Y n j) (C.symm v))
  have hG : G (a i) = C z := by
    dsimp [G, a]
    rw [(c i).left_inv (mem_localChart_source Y e _), s2e_powerFactorSection_base]
  have hf := (s2e_power_coordinates_chart_analytic_at_center Y n d e z).differentiableAt.hasFDerivAt
  have hg := (s2e_powerFactorSection_chart_analytic Y n d e z i).differentiableAt.hasFDerivAt
  change HasFDerivAt F (fderiv ℂ F (C z)) (C z) at hf
  change HasFDerivAt G (fderiv ℂ G (a i)) (a i) at hg
  rw [← hG] at hf
  have hc := hf.comp (a i) hg
  rw [hG] at hc
  have hu := (hasFDerivAt_update (𝕜 := ℂ) a (a i)).congr_of_eventuallyEq
    (s2e_powerFactorSection_chart_coordinates Y n d e z i)
  exact hc.unique hu

/-- The native tuple-coordinate derivative is surjective, using the algebraic factor sections. -/
theorem s2e_power_coordinates_chart_fderiv_surjective
    (Y : Over (Spec ↧ℂ)) (n d e : ℕ)
    [SmoothOfRelativeDimension d (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) :
    let F := fun v => fun i : Fin n =>
      localChart Y e (Point.map (g3_proj Y n i) z)
        (Point.map (g3_proj Y n i) ((localChart (g3_power Y n) d z).symm v))
    Function.Surjective (fderiv ℂ F (localChart (g3_power Y n) d z z)) := by
  dsimp only
  let C := localChart (g3_power Y n) d z
  let c := fun j => localChart Y e (Point.map (g3_proj Y n j) z)
  let a := fun j => c j (Point.map (g3_proj Y n j) z)
  let G := fun i v => C (Point.map (s2e_powerFactorSection Y n z i) ((c i).symm v))
  let F := fun v => fun j => c j (Point.map (g3_proj Y n j) (C.symm v))
  intro w
  refine ⟨∑ i, fderiv ℂ (G i) (a i) (w i), ?_⟩
  change (fderiv ℂ F (C z)) (∑ i, fderiv ℂ (G i) (a i) (w i)) = w
  rw [map_sum]
  have hi : ∀ i, fderiv ℂ F (C z) (fderiv ℂ (G i) (a i) (w i)) = Pi.single i (w i) := by
    intro i
    have h := congrArg (fun L => L (w i)) (s2e_powerFactorSection_chart_fderiv Y n d e z i)
    refine h.trans ?_
    ext j
    by_cases hji : j = i
    · subst j; simp
    · simp [ContinuousLinearMap.pi_apply, hji]
  simp_rw [hi]
  exact Finset.univ_sum_single w

/-- In the product dimension the native tuple-coordinate derivative is bijective. -/
theorem s2e_power_coordinates_chart_fderiv_bijective
    (Y : Over (Spec ↧ℂ)) (n e : ℕ)
    [SmoothOfRelativeDimension (n * e) (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) :
    let F := fun v => fun i : Fin n =>
      localChart Y e (Point.map (g3_proj Y n i) z)
        (Point.map (g3_proj Y n i) ((localChart (g3_power Y n) (n * e) z).symm v))
    Function.Bijective (fderiv ℂ F (localChart (g3_power Y n) (n * e) z z)) := by
  dsimp only
  have hs := s2e_power_coordinates_chart_fderiv_surjective Y n (n * e) e z
  refine ⟨?_, hs⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f :=
    (fderiv ℂ _ (localChart (g3_power Y n) (n * e) z z)).toLinearMap) ?_).2 hs
  simp [Module.finrank_pi_fintype]

/-- Reconstruction from inverse curve charts is a local left inverse in native parameters. -/
theorem s2e_power_chart_lift_left_inverse
    (Y : Over (Spec ↧ℂ)) (n d e : ℕ)
    [SmoothOfRelativeDimension d (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) :
    let C := localChart (g3_power Y n) d z
    let c := fun i => localChart Y e (Point.map (g3_proj Y n i) z)
    let H := fun (w : Fin n → Fin e → ℂ) => C (s2_lift n (fun i => (c i).symm (w i)))
    let F := fun v => fun i => c i (Point.map (g3_proj Y n i) (C.symm v))
    ∀ᶠ v in nhds (C z), H (F v) = v := by
  dsimp only
  let C := localChart (g3_power Y n) d z
  have hz := mem_localChart_source (g3_power Y n) d z
  have ht := C.map_source hz
  obtain ⟨hopen, hmem⟩ := s2e_power_common_chart_neighbourhood Y n e z
  have he : ∀ᶠ v in nhds (C z), ∀ i : Fin n,
      Point.map (g3_proj Y n i) (C.symm v) ∈
        (localChart Y e (Point.map (g3_proj Y n i) z)).source := by
    exact (C.tendsto_symm hz) (hopen.mem_nhds hmem)
  filter_upwards [he, C.open_target.mem_nhds ht] with v hv hvt
  have hh := funext (fun i => (localChart Y e (Point.map (g3_proj Y n i) z)).left_inv (hv i))
  change C (s2_lift n _) = v
  rw [hh]
  change C (s2_lift n (fun i => C.symm v ≫ g3_proj Y n i)) = v
  rw [s2e_lift_coordinates]
  exact C.right_inv hvt

/-- The actual tuple lift is analytic in native charts in the product dimension. -/
theorem s2e_power_chart_lift_analytic
    (Y : Over (Spec ↧ℂ)) (n e : ℕ)
    [SmoothOfRelativeDimension (n * e) (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (g3_power Y n)) :
    AnalyticAt ℂ (fun w => localChart (g3_power Y n) (n * e) z
      (s2_lift n (fun i => (localChart Y e (Point.map (g3_proj Y n i) z)).symm (w i))))
      (fun i => localChart Y e (Point.map (g3_proj Y n i) z) (Point.map (g3_proj Y n i) z)) := by
  let C := localChart (g3_power Y n) (n * e) z
  let c := fun i => localChart Y e (Point.map (g3_proj Y n i) z)
  let F := fun v => fun i => c i (Point.map (g3_proj Y n i) (C.symm v))
  let H := fun (w : Fin n → Fin e → ℂ) => C (s2_lift n (fun i => (c i).symm (w i)))
  have hb := s2e_power_coordinates_chart_fderiv_bijective Y n e z
  let L : (Fin (n * e) → ℂ) ≃L[ℂ] (Fin n → Fin e → ℂ) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℂ F (C z))
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hL : (L : (Fin (n * e) → ℂ) →L[ℂ] (Fin n → Fin e → ℂ)) =
      fderiv ℂ F (C z) := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have ha : AnalyticAt ℂ F (C z) := s2e_power_coordinates_chart_analytic_at_center Y n (n * e) e z
  have hf : HasStrictFDerivAt F (L : _ →L[ℂ] _) (C z) := by
    rw [hL]
    exact ha.hasStrictFDerivAt
  let f := hf.toOpenPartialHomeomorph F
  have hi : AnalyticAt ℂ f.symm (F (C z)) :=
    f.analyticAt_symm' hf.mem_toOpenPartialHomeomorph_source ha hL.symm
  have he : H =ᶠ[nhds (F (C z))] hf.localInverse F L (C z) :=
    hf.localInverse_unique (s2e_power_chart_lift_left_inverse Y n (n * e) e z)
  have hh : AnalyticAt ℂ H (F (C z)) := hi.congr he.symm
  have hz := mem_localChart_source (g3_power Y n) (n * e) z
  simpa only [F, C.left_inv hz] using hh

/-- Evaluation of a projective tuple through a scheme morphism is analytic in native charts. -/
theorem s2e_projective_tuple_map_chart_analytic
    (Y B : Over (Spec ↧ℂ)) [IsProjective Y.hom] (n e b : ℕ)
    [SmoothOfRelativeDimension (n * e) (g3_power Y n).hom]
    [SmoothOfRelativeDimension e Y.hom] [SmoothOfRelativeDimension b B.hom]
    (f : g3_power Y n ⟶ B) (z : ComplexPoint (g3_power Y n)) :
    AnalyticAt ℂ (fun w => localChart B b (Point.map f z)
      (Point.map f (s2_lift n
        (fun i => (localChart Y e (Point.map (g3_proj Y n i) z)).symm (w i)))))
      (fun i => localChart Y e (Point.map (g3_proj Y n i) z) (Point.map (g3_proj Y n i) z)) := by
  let C := localChart (g3_power Y n) (n * e) z
  let c := fun i => localChart Y e (Point.map (g3_proj Y n i) z)
  let a := fun i => c i (Point.map (g3_proj Y n i) z)
  let T := fun (w : Fin n → Fin e → ℂ) => s2_lift n (fun i => (c i).symm (w i))
  have hT : T a = z := by
    dsimp [T, a]
    have hh := funext (fun i => (c i).left_inv (mem_localChart_source Y e _))
    rw [hh]
    exact s2e_lift_coordinates n z
  have hc : ContinuousAt T a := by
    apply (s2e_projective_tuple_lift_continuous Y n).continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    exact ((c i).continuousAt_symm ((c i).map_source (mem_localChart_source Y e _))).comp_of_eq
      (f := fun w : Fin n → Fin e → ℂ => w i) (continuous_apply i).continuousAt rfl
  have hz := mem_localChart_source (g3_power Y n) (n * e) z
  have he : ∀ᶠ w in nhds a, T w ∈ C.source := by
    apply hc
    rw [hT]
    exact C.open_source.mem_nhds hz
  have hf := analyticAt_localChart_symm_map (g3_power Y n) B f (n * e) b z
    (C.map_source hz)
  have hfm : Point.map f (C.symm (C z)) ∈ (localChart B b (Point.map f z)).source := by
    rw [C.left_inv hz]
    exact mem_localChart_source B b _
  have ha := (hf hfm).comp_of_eq (s2e_power_chart_lift_analytic Y n e z)
    (show C (T a) = C z by rw [hT])
  apply ha.congr
  filter_upwards [he] with w hw
  dsimp only [Function.comp_def]
  rw [C.left_inv hw]

end HodgeLean.Foundations.Program

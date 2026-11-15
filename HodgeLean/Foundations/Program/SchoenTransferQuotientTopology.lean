import HodgeLean.Foundations.Program.SchoenTransferQuotientLinear
import Mathlib.Topology.LocallyConstant.Algebra

/-! Topological descent for the actual projective quotient map. -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Analytic
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Surjective maps between projective complex schemes are topological quotient maps. -/
theorem s4_projective_quotientMap
    {T W : Over (Spec ↧ℂ)} [IsProjective T.hom] [IsProjective W.hom]
    (q : T ⟶ W) (hq : Function.Surjective (Point.map q)) :
    Topology.IsQuotientMap (Point.map q) := by
  letI : T2Space (ComplexPoint W) := f4_t2Space W
  have hc : Continuous (Point.map q) := (Point.continuousMap q).continuous
  exact hc.isClosedMap.isQuotientMap hc hq

/-- A locally constant section constant on quotient fibres descends uniquely. -/
theorem s4_locallyConstant_quotient_descent
    {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Topology.IsQuotientMap f) (u : LocallyConstant X R)
    (hu : ∀ x x', f x = f x' → u x = u x') :
    ∃! v : LocallyConstant Y R, ∀ x, v (f x) = u x := by
  classical
  obtain ⟨s, hs⟩ := hf.surjective.hasRightInverse
  let g : Y → R := fun y => u (s y)
  have hg : ∀ x, g (f x) = u x := fun x => hu (s (f x)) x (hs (f x))
  have hgc : IsLocallyConstant g := by
    intro U
    apply hf.isOpen_preimage.mp
    have hpre : f ⁻¹' (g ⁻¹' U) = u ⁻¹' U := by
      ext x
      change g (f x) ∈ U ↔ u x ∈ U
      rw [hg x]
    rw [hpre]
    exact u.isLocallyConstant U
  refine ⟨⟨g, hgc⟩, hg, ?_⟩
  intro v hv
  ext y
  obtain ⟨x, rfl⟩ := hf.surjective y
  exact (hv x).trans (hg x).symm

/-- Invariant locally constant sections descend on each open of the projective quotient. -/
theorem s4_quotient_open_section_descent
    {T W : Over (Spec ↧ℂ)} [IsProjective T.hom] [IsProjective W.hom]
    (q : T ⟶ W) (hq : Function.Surjective (Point.map q))
    {I R : Type*} (a : I → (T ⟶ T))
    (hfib : ∀ x y : ComplexPoint T, Point.map q x = Point.map q y →
      ∃ i, Point.map (a i) x = y)
    (U : TopologicalSpace.Opens (ComplexPoint W))
    (u : LocallyConstant {x : ComplexPoint T // Point.map q x ∈ U} R)
    (hu : ∀ i (x : ComplexPoint T) (hx : Point.map q x ∈ U)
      (hax : Point.map q (Point.map (a i) x) ∈ U),
      u ⟨Point.map (a i) x, hax⟩ = u ⟨x, hx⟩) :
    ∃! v : LocallyConstant U R, ∀ x,
      v ⟨Point.map q x.val, x.property⟩ = u x := by
  apply s4_locallyConstant_quotient_descent ((U : Set (ComplexPoint W)).restrictPreimage (Point.map q))
    ((s4_projective_quotientMap q hq).restrictPreimage_isOpen U.isOpen) u
  intro x y hxy
  have hqxy : Point.map q x.val = Point.map q y.val := congrArg Subtype.val hxy
  obtain ⟨i, hi⟩ := hfib x.val y.val hqxy
  have hax : Point.map q (Point.map (a i) x.val) ∈ U := by
    rw [hi]
    exact y.property
  have h := hu i x.val x.property hax
  have heq : (⟨Point.map (a i) x.val, hax⟩ :
      {x : ComplexPoint T // Point.map q x ∈ U}) = y := Subtype.ext hi
  rw [heq] at h
  exact h.symm

/-- Closed maps shrink a neighborhood of an entire fibre from the base. -/
theorem s4_closedMap_fibre_neighborhood
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsClosedMap f) (y : Y) (V : Set X)
    (hV : IsOpen V) (hyV : f ⁻¹' {y} ⊆ V) :
    ∃ U : TopologicalSpace.Opens Y, y ∈ U ∧ f ⁻¹' (U : Set Y) ⊆ V := by
  let U : TopologicalSpace.Opens Y := ⟨(f '' Vᶜ)ᶜ, (hf Vᶜ hV.isClosed_compl).isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hyV (by exact hxy))
  · intro x hx
    by_contra hnx
    exact hx ⟨x, hnx, rfl⟩

/-- A finite algebraic map has finite fibres on actual complex points. -/
theorem s4_finite_complex_fibres
    {T W : Over (Spec ↧ℂ)} [LocallyOfFiniteType T.hom]
    (q : T ⟶ W) [IsFinite q.left] (y : ComplexPoint W) :
    ((Point.map q) ⁻¹' {y}).Finite := by
  have hi : Function.Injective (Point.underlying : ComplexPoint T → T.left) :=
    underlying_injective_of_locallyOfFiniteType
  apply ((q.left.finite_preimage_singleton y.underlying).preimage hi.injOn).subset
  intro x hx
  change q.left x.underlying = y.underlying
  exact congrArg Point.underlying hx

/-- A finite fibre has disjoint local neighborhoods covering a base shrink. -/
theorem s4_finite_fibre_disjoint_shrink
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsClosedMap f) (y : Y)
    (hfin : (f ⁻¹' {y}).Finite)
    (V : (f ⁻¹' {y}) → TopologicalSpace.Opens X)
    (hV : ∀ x, x.val ∈ V x) :
    ∃ (U : TopologicalSpace.Opens Y) (D : (f ⁻¹' {y}) → TopologicalSpace.Opens X),
      y ∈ U ∧ (∀ x, x.val ∈ D x ∧ D x ≤ V x) ∧
      Pairwise (fun i j => Disjoint (D i : Set X) (D j : Set X)) ∧
      f ⁻¹' (U : Set Y) ⊆ ⋃ x, (D x : Set X) := by
  classical
  obtain ⟨O, hO, hdisj⟩ := hfin.t2_separation
  let D : (f ⁻¹' {y}) → TopologicalSpace.Opens X :=
    fun x => ⟨O x.val ∩ V x, (hO x.val).2.inter (V x).isOpen⟩
  have hD : ∀ x, x.val ∈ D x ∧ D x ≤ V x :=
    fun x => ⟨⟨(hO x.val).1, hV x⟩, fun _ h => h.2⟩
  obtain ⟨U, hyU, hU⟩ := s4_closedMap_fibre_neighborhood f hf y
    (⋃ x, (D x : Set X)) (isOpen_iUnion fun x => (D x).isOpen)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hD ⟨x, hx⟩).1⟩)
  refine ⟨U, D, hyU, hD, ?_, hU⟩
  intro i j hij
  exact (hdisj i.property j.property (fun h => hij (Subtype.ext h))).mono
    Set.inter_subset_left Set.inter_subset_left

/-- Rational averaging of actual pullbacks of locally constant sections. -/
noncomputable def s4_locallyConstant_average
    {X G : Type*} [TopologicalSpace X] [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) :
    Module.End ℚ (LocallyConstant X ℚ) :=
  (Fintype.card G : ℚ)⁻¹ • ∑ g : G,
    LocallyConstant.comapₗ ℚ ⟨fun x : X => g • x, hc g⟩

/-- Evaluate the rational section average as the finite orbit sum. -/
theorem s4_locallyConstant_average_apply
    {X G : Type*} [TopologicalSpace X] [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (u : LocallyConstant X ℚ) (x : X) :
    s4_locallyConstant_average hc u x =
      (Fintype.card G : ℚ)⁻¹ * ∑ g : G, u (g • x) := by
  simp only [s4_locallyConstant_average, LinearMap.smul_apply, LinearMap.sum_apply,
    LocallyConstant.smul_apply, smul_eq_mul]
  congr 1
  exact map_sum (LocallyConstant.evalAddMonoidHom x) _ _

/-- Rational averaging gives an invariant section even over points with stabilizers. -/
theorem s4_locallyConstant_average_invariant
    {X G : Type*} [TopologicalSpace X] [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (u : LocallyConstant X ℚ) (h : G) (x : X) :
    s4_locallyConstant_average hc u (h • x) = s4_locallyConstant_average hc u x := by
  rw [s4_locallyConstant_average_apply, s4_locallyConstant_average_apply]
  congr 1
  have he := Equiv.sum_comp (Equiv.mulRight h) (fun g => u (g • x))
  change (∑ g : G, u ((g * h) • x)) = ∑ g : G, u (g • x) at he
  simpa only [mul_smul] using he

/-- Rational averaging fixes every invariant section. -/
theorem s4_locallyConstant_average_fixed
    {X G : Type*} [TopologicalSpace X] [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (u : LocallyConstant X ℚ) (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    s4_locallyConstant_average hc u = u := by
  ext x
  rw [s4_locallyConstant_average_apply]
  simp only [hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

/-- The averaged section belongs to the image of actual quotient pullback. -/
theorem s4_average_mem_quotient_range
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (f : C(X, Y)) (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (u : LocallyConstant X ℚ) :
    s4_locallyConstant_average hc u ∈ LinearMap.range (LocallyConstant.comapₗ ℚ f) := by
  obtain ⟨v, hv, _⟩ := s4_locallyConstant_quotient_descent f hf
    (s4_locallyConstant_average hc u) (by
      intro x y hxy
      obtain ⟨g, hg⟩ := horb x y hxy
      rw [← hg]
      exact (s4_locallyConstant_average_invariant hc u g x).symm)
  refine ⟨v, ?_⟩
  ext x
  exact hv x

/-- The normalized section transfer is a linear lift of actual averaging. -/
noncomputable def s4_quotient_sectionTransfer
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (f : C(X, Y)) (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y) :
    LocallyConstant X ℚ →ₗ[ℚ] LocallyConstant Y ℚ :=
  (LinearEquiv.ofInjective (LocallyConstant.comapₗ ℚ f)
    (LocallyConstant.comap_injective f hf.surjective)).symm.toLinearMap.comp
      ((s4_locallyConstant_average hc).codRestrict _
        (s4_average_mem_quotient_range hc f hf horb))

/-- Pulling a transferred section back gives its actual finite-group average. -/
theorem s4_quotient_sectionTransfer_pullback
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (f : C(X, Y)) (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (u : LocallyConstant X ℚ) :
    LocallyConstant.comapₗ ℚ f (s4_quotient_sectionTransfer hc f hf horb u) =
      s4_locallyConstant_average hc u := by
  exact LinearEquiv.ofInjective_symm_apply (LocallyConstant.comapₗ ℚ f)
    (h := LocallyConstant.comap_injective f hf.surjective)
    ⟨s4_locallyConstant_average hc u, s4_average_mem_quotient_range hc f hf horb u⟩

/-- Transfer retracts quotient pullback on rational locally constant sections. -/
theorem s4_quotient_sectionTransfer_retraction
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (f : C(X, Y)) (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) :
    (s4_quotient_sectionTransfer hc f hf horb).comp (LocallyConstant.comapₗ ℚ f) =
      LinearMap.id := by
  apply LinearMap.ext
  intro u
  apply LocallyConstant.comap_injective f hf.surjective
  change LocallyConstant.comapₗ ℚ f
    (s4_quotient_sectionTransfer hc f hf horb (LocallyConstant.comapₗ ℚ f u)) =
      LocallyConstant.comapₗ ℚ f u
  rw [s4_quotient_sectionTransfer_pullback]
  apply s4_locallyConstant_average_fixed hc
  intro g x
  exact congrArg u (hfg g x)

/-- Actual quotient section pullback has precisely the invariant image. -/
theorem s4_quotient_section_invariant_range
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (f : C(X, Y)) (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) :
    LinearMap.range (LocallyConstant.comapₗ ℚ f) =
      ⨅ g : G, LinearMap.ker
        (LocallyConstant.comapₗ ℚ (Z := ℚ) ⟨fun x : X => g • x, hc g⟩ - (LinearMap.id : Module.End ℚ (LocallyConstant X ℚ))) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    ext x
    exact congrArg v (hfg g x)
  · intro u hu
    have hgu : ∀ g : G,
        LocallyConstant.comapₗ ℚ (Z := ℚ) ⟨fun x : X => g • x, hc g⟩ u = u := by
      simpa only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] using hu
    obtain ⟨v, hv, _⟩ := s4_locallyConstant_quotient_descent f hf u (by
      intro x y hxy
      obtain ⟨g, hg⟩ := horb x y hxy
      rw [← hg]
      exact (congrArg (fun w : LocallyConstant X ℚ => w x) (hgu g)).symm)
    refine ⟨v, ?_⟩
    ext x
    exact hv x

/-- Normalized section transfer is natural for equivariant quotient squares. -/
theorem s4_quotient_sectionTransfer_naturality
    {X X' Y Y' G : Type*} [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    [Group G] [Fintype G] [MulAction G X] [MulAction G X']
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (hc' : ∀ g : G, Continuous (fun x : X' => g • x))
    (f : C(X, Y)) (f' : C(X', Y'))
    (hf : Topology.IsQuotientMap f) (hf' : Topology.IsQuotientMap f')
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (horb' : ∀ x y : X', f' x = f' y → ∃ g : G, g • x = y)
    (i : C(X', X)) (j : C(Y', Y))
    (hsquare : ∀ x, f (i x) = j (f' x))
    (hequiv : ∀ (g : G) (x : X'), i (g • x) = g • i x) :
    (s4_quotient_sectionTransfer hc' f' hf' horb').comp (LocallyConstant.comapₗ ℚ i) =
      (LocallyConstant.comapₗ ℚ j).comp (s4_quotient_sectionTransfer hc f hf horb) := by
  apply LinearMap.ext
  intro u
  apply LocallyConstant.ext
  intro y
  obtain ⟨x, rfl⟩ := hf'.surjective y
  have h₁ := congrArg (fun v : LocallyConstant X' ℚ => v x)
    (s4_quotient_sectionTransfer_pullback hc' f' hf' horb'
      (LocallyConstant.comapₗ ℚ i u))
  have h₂ := congrArg (fun v : LocallyConstant X ℚ => v (i x))
    (s4_quotient_sectionTransfer_pullback hc f hf horb u)
  change s4_quotient_sectionTransfer hc' f' hf' horb'
      (LocallyConstant.comapₗ ℚ i u) (f' x) =
    s4_quotient_sectionTransfer hc f hf horb u (j (f' x))
  rw [← hsquare x]
  calc
    _ = s4_locallyConstant_average hc' (LocallyConstant.comapₗ ℚ i u) x := h₁
    _ = s4_locallyConstant_average hc u (i x) := by
      rw [s4_locallyConstant_average_apply, s4_locallyConstant_average_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      exact congrArg u (hequiv g x)
    _ = s4_quotient_sectionTransfer hc f hf horb u (f (i x)) := h₂.symm

end HodgeLean.Foundations.Program

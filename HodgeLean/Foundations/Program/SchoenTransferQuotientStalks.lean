import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Functors
import HodgeLean.Foundations.Program.SchoenTransferQuotientTopology
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Abelian

/-! Fibrewise detection of sections for the quotient direct image. -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ComplexPoint
universe u
namespace HodgeLean.Foundations.Program

/-- Equal germs along a closed-map fibre give equal sections after a base shrink. -/
theorem s4_sections_equal_near_fibre
    {X Y : TopCat} (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat X) (U : Opens Y) (y : Y) (hy : y ∈ U)
    (s t : F.obj.obj (op ((Opens.map f).obj U)))
    (h : ∀ x : X, ∀ hx : f x = y,
      TopCat.Presheaf.germ F.obj ((Opens.map f).obj U) x (by change f x ∈ U; rw [hx]; exact hy) s =
        TopCat.Presheaf.germ F.obj ((Opens.map f).obj U) x (by change f x ∈ U; rw [hx]; exact hy) t) :
    ∃ (V : Opens Y) (hVU : V ≤ U), y ∈ V ∧
      F.obj.map ((Opens.map f).map (homOfLE hVU)).op s =
        F.obj.map ((Opens.map f).map (homOfLE hVU)).op t := by
  classical
  let A := (Opens.map f).obj U
  choose O hxO i₁ i₂ heq using fun x : f ⁻¹' {y} =>
    TopCat.Presheaf.germ_eq F.obj x.val (show x.val ∈ A from (by change f x.val ∈ U; rw [show f x.val = y from x.property]; exact hy))
      (show x.val ∈ A from (by change f x.val ∈ U; rw [show f x.val = y from x.property]; exact hy)) s t (h x.val x.property)
  let W : Opens X := ⨆ x, O x
  have hWA : W ≤ A := iSup_le fun x => (i₁ x).le
  have hW : F.obj.map (homOfLE hWA).op s = F.obj.map (homOfLE hWA).op t := by
    apply F.eq_of_locally_eq' O W (fun x => homOfLE (le_iSup O x)) le_rfl
    intro x
    simp only [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    have hc : (homOfLE hWA).op ≫ (homOfLE (le_iSup O x)).op = (i₁ x).op :=
      Subsingleton.elim _ _
    rw [hc]
    exact (heq x).trans (by rw [Subsingleton.elim (i₂ x) (i₁ x)])
  obtain ⟨B, hyB, hBW⟩ := s4_closedMap_fibre_neighborhood f hf y W W.isOpen
    (fun x hx => (le_iSup O ⟨x, hx⟩) (hxO ⟨x, hx⟩))
  let V := B ⊓ U
  have hVW : (Opens.map f).obj V ≤ W := fun _ hx => hBW hx.1
  refine ⟨V, inf_le_right, ⟨hyB, hy⟩, ?_⟩
  have hh := congrArg (F.obj.map (homOfLE hVW).op) hW
  have hc : (homOfLE hWA).op ≫ (homOfLE hVW).op =
      ((Opens.map f).map (homOfLE (show V ≤ U from inf_le_right))).op :=
    Subsingleton.elim _ _
  simpa only [← ConcreteCategory.comp_apply, ← F.obj.map_comp, hc] using hh

/-- Sections over pairwise disjoint opens form a compatible sheaf family. -/
theorem s4_disjoint_sections_compatible
    {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {I : Type*} (D : I → Opens X)
    (hD : Pairwise (fun i j => Disjoint (D i : Set X) (D j : Set X)))
    (s : ∀ i, F.obj.obj (op (D i))) :
    TopCat.Presheaf.IsCompatible F.obj D s := by
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · apply TopCat.Presheaf.section_ext F (D i ⊓ D j)
    intro x hx
    exact (Set.disjoint_left.mp (hD hij) hx.1 hx.2).elim

/-- Local lifts on a finite closed-map fibre glue after shrinking the base. -/
theorem s4_section_lift_near_finite_fibre
    {X Y : TopCat.{u}} [T2Space X] (f : X ⟶ Y) (hf : IsClosedMap f)
    (F G : TopCat.Sheaf AddCommGrpCat.{u} X) (φ : F ⟶ G)
    (U : Opens Y) (y : Y) (hy : y ∈ U) (hfin : (f ⁻¹' {y}).Finite)
    (t : G.obj.obj (op ((Opens.map f).obj U)))
    (h : ∀ x : f ⁻¹' {y}, ∃ (V : Opens X) (hVA : V ≤ (Opens.map f).obj U)
      (s : F.obj.obj (op V)), x.val ∈ V ∧
        φ.hom.app (op V) s = G.obj.map (homOfLE hVA).op t) :
    ∃ (B : Opens Y) (hBU : B ≤ U), y ∈ B ∧
      ∃ s : F.obj.obj (op ((Opens.map f).obj B)),
        φ.hom.app (op ((Opens.map f).obj B)) s =
          G.obj.map ((Opens.map f).map (homOfLE hBU)).op t := by
  classical
  let A := (Opens.map f).obj U
  choose V hVA s hxV hs using h
  obtain ⟨B, D, hyB, hD, hdisj, hBD⟩ :=
    s4_finite_fibre_disjoint_shrink f hf y hfin V hxV
  let W : Opens X := ⨆ x, D x
  have hWA : W ≤ A := iSup_le fun x => (hD x).2.trans (hVA x)
  let sx : ∀ x, F.obj.obj (op (D x)) :=
    fun x => F.obj.map (homOfLE (hD x).2).op (s x)
  have hsx (x) : φ.hom.app (op (D x)) (sx x) =
      G.obj.map (homOfLE ((hD x).2.trans (hVA x))).op t := by
    dsimp only [sx]
    rw [← ConcreteCategory.comp_apply, φ.hom.naturality, ConcreteCategory.comp_apply,
      hs x, ← ConcreteCategory.comp_apply, ← G.obj.map_comp]
    congr 2
  obtain ⟨z, hz, _⟩ := F.existsUnique_gluing D sx
    (s4_disjoint_sections_compatible F D hdisj sx)
  have hzφ : φ.hom.app (op W) z = G.obj.map (homOfLE hWA).op t := by
    apply G.eq_of_locally_eq' D W (fun x => homOfLE (le_iSup D x)) le_rfl
    intro x
    have hzx := hz x
    rw [show Opens.leSupr D x = homOfLE (le_iSup D x) from Subsingleton.elim _ _] at hzx
    rw [← ConcreteCategory.comp_apply, ← φ.hom.naturality,
      ConcreteCategory.comp_apply, hzx, hsx x,
      ← ConcreteCategory.comp_apply, ← G.obj.map_comp]
    congr 2
  let C := B ⊓ U
  have hCW : (Opens.map f).obj C ≤ W := by
    intro x hx
    exact Opens.mem_iSup.mpr (Set.mem_iUnion.mp (hBD hx.1))
  refine ⟨C, inf_le_right, ⟨hyB, hy⟩, F.obj.map (homOfLE hCW).op z, ?_⟩
  rw [← ConcreteCategory.comp_apply, φ.hom.naturality, ConcreteCategory.comp_apply,
    hzφ, ← ConcreteCategory.comp_apply, ← G.obj.map_comp]
  congr 2

/-- Direct image along a finite-fibre closed map preserves local surjectivity. -/
theorem s4_finite_closed_pushforward_locallySurjective
    {X Y : TopCat.{u}} [T2Space X] (f : X ⟶ Y) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite)
    (F G : TopCat.Sheaf AddCommGrpCat.{u} X) (φ : F ⟶ G)
    (hφ : TopCat.Presheaf.IsLocallySurjective φ.hom) :
    TopCat.Presheaf.IsLocallySurjective
      (((TopCat.Sheaf.pushforward AddCommGrpCat f).map φ).hom) := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U t y hy
  obtain ⟨B, hBU, hyB, s, hs⟩ := s4_section_lift_near_finite_fibre f hf F G φ U y hy
    (hfin y) t (by
      intro x
      have hx : x.val ∈ (Opens.map f).obj U := by
        change f x.val ∈ U
        rw [show f x.val = y from x.property]
        exact hy
      obtain ⟨V, hVA, ⟨s, hs⟩, hxV⟩ :=
        (TopCat.Presheaf.isLocallySurjective_iff φ.hom).mp hφ
          ((Opens.map f).obj U) t x.val hx
      exact ⟨V, hVA, s, hxV, hs⟩)
  exact ⟨B, hBU, ⟨s, hs⟩, hyB⟩

/-- Finite-fibre closed-map direct image preserves epimorphisms of abelian sheaves. -/
theorem s4_finite_closed_pushforward_preservesEpimorphisms
    {X Y : TopCat.{u}} [T2Space X] (f : X ⟶ Y) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesEpimorphisms := by
  constructor
  intro F G φ hφ
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  apply s4_finite_closed_pushforward_locallySurjective f hf hfin F G φ
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi φ).mpr hφ

/-- Direct image for a finite-fibre closed map is exact on abelian sheaves. -/
theorem s4_finite_closed_pushforward_exact
    {X Y : TopCat.{u}} [T2Space X] (f : X ⟶ Y) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesHomology := by
  letI := s4_finite_closed_pushforward_preservesEpimorphisms f hf hfin
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Exact direct image applies to finite projective maps with singular targets. -/
theorem s4_finite_projective_pushforward_exact
    {T W : Over (Spec ↧ℂ)}
    [IsProjective T.hom] [IsProjective W.hom]
    (q : T ⟶ W) [IsFinite q.left] :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0}
      (TopCat.ofHom (Point.continuousMap q))).PreservesHomology := by
  letI : T2Space (ComplexPoint T) :=
    HodgeLean.Foundations.Analytic.f4_t2Space T
  have hc : Continuous (Point.map q) :=
    (Point.continuousMap q).continuous
  exact s4_finite_closed_pushforward_exact
    (TopCat.ofHom (Point.continuousMap q)) hc.isClosedMap
      (s4_finite_complex_fibres q)

/-- Sheaf direct image preserves injective objects via exact inverse image. -/
theorem s4_pushforward_preservesInjectives
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).PreservesInjectiveObjects := by
  letI : RepresentablyFlat (Opens.map f) :=
    flat_of_preservesFiniteLimits (Opens.map f)
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := by
    dsimp only [TopCat.Sheaf.pullback]
    exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
      (Opens.map f) AddCommGrpCat _ _
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f)

/-- Exact finite direct image gives the full derived adjunction on abelian sheaves. -/
noncomputable def s4_finite_closed_extEquiv
    {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite)
    (E : TopCat.Sheaf AddCommGrpCat.{0} Y)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    Abelian.Ext ((TopCat.Sheaf.pullback AddCommGrpCat f).obj E) F n ≃+
      Abelian.Ext E ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n := by
  letI : RepresentablyFlat (Opens.map f) :=
    flat_of_preservesFiniteLimits (Opens.map f)
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat f) := by
    dsimp only [TopCat.Sheaf.pullback]
    exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
      (Opens.map f) AddCommGrpCat _ _
  letI : (TopCat.Sheaf.pullback AddCommGrpCat f).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat f).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI := s4_finite_closed_pushforward_exact f hf hfin
  letI : PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat f) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).extEquiv

/-- Constant abelian sheaves commute with inverse image on topological spaces. -/
noncomputable def s4_constantSheaf_pullbackIso
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0} ⋙
      TopCat.Sheaf.pullback AddCommGrpCat f ≅
        constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} := by
  let aY := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
    (isTerminalTop : IsTerminal (⊤ : Opens Y))
  let aX := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat
    (isTerminalTop : IsTerminal (⊤ : Opens X))
  exact (aY.comp (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f)).leftAdjointUniq aX

attribute [local instance] Abelian.Ext.instAddCommGroup

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Finite closed-map direct image identifies sheaf cohomology in every degree. -/
noncomputable def s4_finite_closed_sheafCohomologyEquiv
    {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n ≃+
      CategoryTheory.Sheaf.H.{0} F n := by
  let A : AddCommGrpCat.{0} := AddCommGrpCat.of (ULift ℤ)
  let E := (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj A
  let e := (s4_constantSheaf_pullbackIso f).app A
  exact (s4_finite_closed_extEquiv f hf hfin E F n).symm.trans
    (((Abelian.extFunctor.{0} n).mapIso e.symm.op).app F).addCommGroupIsoToAddEquiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The sheaf-cohomology comparison for the actual finite projective morphism. -/
noncomputable def s4_finite_projective_sheafCohomologyEquiv
    {T W : Over (Spec ↧ℂ)} [IsProjective T.hom] [IsProjective W.hom]
    (q : T ⟶ W) [IsFinite q.left]
    (F : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (ComplexPoint T))) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} ((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.ofHom (Point.continuousMap q))).obj F) n ≃+
      CategoryTheory.Sheaf.H.{0} F n := by
  letI : T2Space (ComplexPoint T) := HodgeLean.Foundations.Analytic.f4_t2Space T
  have hc : Continuous (Point.map q) := (Point.continuousMap q).continuous
  exact s4_finite_closed_sheafCohomologyEquiv
    (TopCat.ofHom (Point.continuousMap q)) hc.isClosedMap (s4_finite_complex_fibres q) F n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Finite-map derived adjunction commutes with actual coefficient morphisms. -/
theorem s4_finite_closed_extEquiv_symm_naturality
    {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite)
    (E : TopCat.Sheaf AddCommGrpCat.{0} Y)
    {F F' : TopCat.Sheaf AddCommGrpCat.{0} X} (u : F ⟶ F') (n : ℕ)
    (z : Abelian.Ext E ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n) :
    (s4_finite_closed_extEquiv f hf hfin E F' n).symm
      (z.comp (Abelian.Ext.mk₀ ((TopCat.Sheaf.pushforward AddCommGrpCat f).map u))
        (add_zero n)) =
      ((s4_finite_closed_extEquiv f hf hfin E F n).symm z).comp
        (Abelian.Ext.mk₀ u) (add_zero n) := by
  letI : RepresentablyFlat (Opens.map f) :=
    flat_of_preservesFiniteLimits (Opens.map f)
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat f) := by
    dsimp only [TopCat.Sheaf.pullback]
    exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
      (Opens.map f) AddCommGrpCat _ _
  letI : (TopCat.Sheaf.pullback AddCommGrpCat f).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat f).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI := s4_finite_closed_pushforward_exact f hf hfin
  letI : PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat f) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).extEquiv_symm_naturality_right₀ z u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The finite-map cohomology comparison is natural in the coefficient sheaf. -/
theorem s4_finite_closed_sheafCohomologyEquiv_naturality
    {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite)
    {F F' : TopCat.Sheaf AddCommGrpCat.{0} X} (u : F ⟶ F') (n : ℕ)
    (z : CategoryTheory.Sheaf.H.{0}
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n) :
    s4_finite_closed_sheafCohomologyEquiv f hf hfin F' n
      (CategoryTheory.Sheaf.H.map ((TopCat.Sheaf.pushforward AddCommGrpCat f).map u) n z) =
    CategoryTheory.Sheaf.H.map u n
      (s4_finite_closed_sheafCohomologyEquiv f hf hfin F n z) := by
  let A : AddCommGrpCat.{0} := AddCommGrpCat.of (ULift ℤ)
  let E := (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj A
  let e := (s4_constantSheaf_pullbackIso f).app A
  change (Abelian.Ext.mk₀ e.inv).comp
    ((s4_finite_closed_extEquiv f hf hfin E F' n).symm
      (z.comp (Abelian.Ext.mk₀ ((TopCat.Sheaf.pushforward AddCommGrpCat f).map u))
        (add_zero n))) (zero_add n) =
    ((Abelian.Ext.mk₀ e.inv).comp
      ((s4_finite_closed_extEquiv f hf hfin E F n).symm z) (zero_add n)).comp
        (Abelian.Ext.mk₀ u) (add_zero n)
  rw [s4_finite_closed_extEquiv_symm_naturality]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

end HodgeLean.Foundations.Program

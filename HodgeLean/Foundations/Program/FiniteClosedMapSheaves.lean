module

public import HodgeLean.Foundations.Program.FiniteClosedMapNeighborhoods
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Colimits

public section
open CategoryTheory TopologicalSpace Opposite
universe u
namespace HodgeLean.Foundations.Program

/-- Sections on disjoint open sets glue without additional compatibility data. -/
theorem sheaf_gluing_of_pairwiseDisjoint
    {A : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} A)
    {ι : Type u} (U : ι → Opens A) (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (s : ∀ i, F.obj.obj (op (U i))) :
    ∃ t : F.obj.obj (op (iSup U)),
      ∀ i, F.obj.map (Opens.leSupr U i).op t = s i := by
  obtain ⟨t, ht, _⟩ := F.existsUnique_gluing U s (by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · apply TopCat.Presheaf.section_ext F
      intro x hx
      exact False.elim ((Set.disjoint_left.mp (Opens.coe_disjoint.mpr (hU hij))) hx.1 hx.2))
  exact ⟨t, ht⟩

/-- Local lifts along a sheaf map on disjoint opens give a lift on their union. -/
theorem sheaf_lift_on_disjoint_union
    {A : TopCat.{u}} {F H : TopCat.Sheaf AddCommGrpCat.{u} A}
    (f : F ⟶ H) {ι : Type u} (U : ι → Opens A)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (W : Opens A) (hle : ∀ i, U i ≤ W) (t : H.obj.obj (op W))
    (s : ∀ i, F.obj.obj (op (U i)))
    (hs : ∀ i, f.hom.app (op (U i)) (s i) =
      H.obj.map (homOfLE (hle i)).op t) :
    ∃ r : F.obj.obj (op (iSup U)),
      f.hom.app (op (iSup U)) r =
        H.obj.map (homOfLE (iSup_le hle)).op t := by
  obtain ⟨r, hr⟩ := sheaf_gluing_of_pairwiseDisjoint F U hU s
  refine ⟨r, ?_⟩
  apply H.eq_of_locally_eq U
  intro i
  rw [← ConcreteCategory.comp_apply, ← f.hom.naturality,
    ConcreteCategory.comp_apply, hr, hs]
  rw [← ConcreteCategory.comp_apply, ← H.obj.map_comp]
  rfl

/-- A locally surjective sheaf map lifts sections on the preimage of a small
neighborhood of any finite fibre of a closed continuous map. -/
theorem finite_closedMap_local_section_lift
    {A B : TopCat.{u}} [T2Space A] (q : A ⟶ B) (hq : IsClosedMap q)
    {F H : TopCat.Sheaf AddCommGrpCat.{u} A} (f : F ⟶ H)
    (hf : TopCat.Presheaf.IsLocallySurjective f.hom)
    (W : Opens A) (t : H.obj.obj (op W)) (y : B)
    (hfinite : (q ⁻¹' {y}).Finite) (hfibre : q ⁻¹' {y} ⊆ W) :
    ∃ (V : Opens B) (hy : y ∈ V) (hle : (Opens.map q).obj V ≤ W)
      (s : F.obj.obj (op ((Opens.map q).obj V))),
      f.hom.app (op ((Opens.map q).obj V)) s =
        H.obj.map (homOfLE hle).op t := by
  classical
  have hlocal : ∀ x : A, ∃ (O : Opens A) (hOW : O ≤ W),
      (x ∈ q ⁻¹' {y} → x ∈ O ∧ ∃ s : F.obj.obj (op O),
        f.hom.app (op O) s = H.obj.map (homOfLE hOW).op t) := by
    intro x
    by_cases hx : x ∈ q ⁻¹' {y}
    · obtain ⟨O, hle, hs, hxO⟩ :=
        (TopCat.Presheaf.isLocallySurjective_iff f.hom).mp hf W t x (hfibre hx)
      exact ⟨O, hle, fun _ => ⟨hxO, hs⟩⟩
    · exact ⟨⊥, bot_le, fun h => False.elim (hx h)⟩
  choose O hle hlocal using hlocal
  obtain ⟨R, V, hR, hdisj, hV, hy, hpre⟩ :=
    finite_closedMap_disjoint_fibre_neighborhoods hq y hfinite
      (fun x => (O x : Set A)) (fun x hx => ⟨(O x).isOpen, (hlocal x hx).1⟩)
  let U : (q ⁻¹' {y}) → Opens A := fun x => ⟨R x, (hR x x.property).1⟩
  have hUle : ∀ x, U x ≤ O x := fun x => (hR x x.property).2.2
  have hUW : ∀ x, U x ≤ W := fun x => (hUle x).trans (hle x)
  have hs : ∀ x : q ⁻¹' {y}, ∃ s : F.obj.obj (op (U x)),
      f.hom.app (op (U x)) s = H.obj.map (homOfLE (hUW x)).op t := by
    intro x
    obtain ⟨s, hs⟩ := (hlocal x x.property).2
    refine ⟨F.obj.map (homOfLE (hUle x)).op s, ?_⟩
    rw [← ConcreteCategory.comp_apply, f.hom.naturality,
      ConcreteCategory.comp_apply, hs, ← ConcreteCategory.comp_apply, ← H.obj.map_comp]
    rfl
  choose s hs using hs
  have hpair : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    apply Opens.coe_disjoint.mp
    exact hdisj i.property j.property (fun h => hij (Subtype.ext h))
  obtain ⟨r, hr⟩ := sheaf_lift_on_disjoint_union f U hpair W hUW t s hs
  let V' : Opens B := ⟨V, hV⟩
  have hUV : (Opens.map q).obj V' ≤ iSup U := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hpre hx)
    exact Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hxz⟩
  refine ⟨V', hy, hUV.trans (iSup_le hUW),
    F.obj.map (homOfLE hUV).op r, ?_⟩
  rw [← ConcreteCategory.comp_apply, f.hom.naturality,
    ConcreteCategory.comp_apply, hr, ← ConcreteCategory.comp_apply, ← H.obj.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Pushforward by a closed map with finite fibres preserves local surjectivity
of morphisms of abelian sheaves. -/
theorem finite_closedMap_pushforward_locallySurjective
    {A B : TopCat.{u}} [T2Space A] (q : A ⟶ B) (hq : IsClosedMap q)
    (hfinite : ∀ y, (q ⁻¹' {y}).Finite)
    {F H : TopCat.Sheaf AddCommGrpCat.{u} A} (f : F ⟶ H)
    (hf : TopCat.Presheaf.IsLocallySurjective f.hom) :
    TopCat.Presheaf.IsLocallySurjective
      ((TopCat.Sheaf.pushforward AddCommGrpCat q).map f).hom := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U t y hy
  obtain ⟨V, hyV, hle, s, hs⟩ := finite_closedMap_local_section_lift q hq f hf
    ((Opens.map q).obj U) t y (hfinite y) (by
      intro x hx
      change q x ∈ U
      have hxy : q x = y := hx
      exact hxy ▸ hy)
  let W := V ⊓ U
  have hWV : (Opens.map q).obj W ≤ (Opens.map q).obj V :=
    fun _ hx => hx.1
  refine ⟨W, inf_le_right, ⟨F.obj.map (homOfLE hWV).op s, ?_⟩, hyV, hy⟩
  change f.hom.app (op ((Opens.map q).obj W))
    (F.obj.map (homOfLE hWV).op s) =
      H.obj.map (homOfLE (show (Opens.map q).obj W ≤ (Opens.map q).obj U
        from fun _ hx => hx.2)).op t
  rw [← ConcreteCategory.comp_apply, f.hom.naturality,
    ConcreteCategory.comp_apply, hs, ← ConcreteCategory.comp_apply, ← H.obj.map_comp]
  rfl

/-- Pushforward by a closed map with finite fibres preserves epimorphisms
of abelian sheaves. -/
theorem finite_closedMap_pushforward_epi
    {A B : TopCat.{u}} [T2Space A] (q : A ⟶ B) (hq : IsClosedMap q)
    (hfinite : ∀ y, (q ⁻¹' {y}).Finite)
    {F H : TopCat.Sheaf AddCommGrpCat.{u} A} (f : F ⟶ H) [Epi f] :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat q).map f) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  apply finite_closedMap_pushforward_locallySurjective q hq hfinite f
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi f).mpr inferInstance

/-- Finite closed pushforward preserves homology of complexes of abelian sheaves. -/
theorem finite_closedMap_pushforward_preservesHomology
    {A B : TopCat.{u}} [T2Space A] (q : A ⟶ B) (hq : IsClosedMap q)
    (hfinite : ∀ y, (q ⁻¹' {y}).Finite) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} q).PreservesHomology := by
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} q).PreservesEpimorphisms :=
    ⟨fun f => finite_closedMap_pushforward_epi q hq hfinite f⟩
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

end HodgeLean.Foundations.Program

module

public import HodgeLean.Foundations.Program.SchoenExceptionalSoftAcyclic
public import HodgeLean.Foundations.Program.SchoenExceptionalProper
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Functor.Flat

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry
namespace HodgeLean.Foundations.Program


theorem s3_pullback_preservesFiniteLimits {X Y : TopCat.{0}} (i : X ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} i) := by
  letI : RepresentablyFlat (Opens.map i) :=
    flat_of_preservesFiniteLimits (Opens.map i)
  exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map i) AddCommGrpCat.{0} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)

 theorem s3_pullback_shortExact {X Y : TopCat.{0}} (i : X ⟶ Y)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} Y)} (hS : S.ShortExact) :
    (S.map (TopCat.Sheaf.pullback AddCommGrpCat.{0} i)).ShortExact := by
  letI := s3_pullback_preservesFiniteLimits i
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map _

 theorem s3_pushforward_injective {X Y : TopCat.{0}} (p : X ⟶ Y)
    (I : TopCat.Sheaf AddCommGrpCat.{0} X) [Injective I] :
    Injective ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj I) := by
  letI := s3_pullback_preservesFiniteLimits p
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} p).map_injective I inferInstance

 theorem s3_fibre_injective_acyclic {X Y : TopCat.{0}} [T2Space X] [LocallyCompactSpace X]
    (p : X ⟶ Y) (hp : IsProperMap p) (I : TopCat.Sheaf AddCommGrpCat.{0} X)
    [Injective I] (y : Y) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (s3_fibreInclusion p y)).obj I) (n + 1)) := by
  let : CompactSpace {x : X // p x = y} := s3_fibre_compactSpace p hp y
  have := TopCat.Sheaf.injective_isFlasque X I
  exact s3_subsingleton_cohomology_succ_of_isSoft _
    (s3_pullback_isSoft_of_isFlasque (s3_fibreInclusion p y)
      (show Topology.IsEmbedding (s3_fibreInclusion p y) from
        Topology.IsEmbedding.subtypeVal) I) n


attribute [local instance] TopCat.Sheaf.extAddCommGroup

set_option backward.isDefEq.respectTransparency false in
theorem s3_fibre_cokernel_acyclic {X Y : TopCat.{0}} [T2Space X] [LocallyCompactSpace X]
    (p : X ⟶ Y) (hp : IsProperMap p)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
    [Injective S.X₂]
    (hF : ∀ (y : Y) (n : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (s3_fibreInclusion p y)).obj S.X₁) (n + 1)))
    (y : Y) (n : ℕ) : Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (s3_fibreInclusion p y)).obj S.X₃) (n + 1)) := by
  let R := S.map (TopCat.Sheaf.pullback AddCommGrpCat.{0} (s3_fibreInclusion p y))
  have hR : R.ShortExact := s3_pullback_shortExact _ hS
  let : Subsingleton (CategoryTheory.Sheaf.H R.X₁ (n + 2)) := hF y (n + 1)
  let : Subsingleton (CategoryTheory.Sheaf.H R.X₂ (n + 1)) :=
    s3_fibre_injective_acyclic p hp S.X₂ y n
  letI : AddCommGroup (CategoryTheory.Sheaf.H R.X₁ (n + 2)) := Abelian.Ext.instAddCommGroup
  letI : AddCommGroup (CategoryTheory.Sheaf.H R.X₂ (n + 1)) := Abelian.Ext.instAddCommGroup
  letI : AddCommGroup (CategoryTheory.Sheaf.H R.X₃ (n + 1)) := Abelian.Ext.instAddCommGroup
  have hz : ∀ x : CategoryTheory.Sheaf.H R.X₃ (n + 1), x = 0 := by
    intro x
    have hx : x.comp hR.extClass (by omega : n + 1 + 1 = n + 2) = 0 :=
      Subsingleton.elim _ _
    obtain ⟨a, ha⟩ := Abelian.Ext.covariant_sequence_exact₃ _ hR x (by omega) hx
    have ha0 : a = 0 := Subsingleton.elim _ _
    rw [← ha, ha0]
    exact Abelian.Ext.zero_comp _ _ _ _ _
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end HodgeLean.Foundations.Program

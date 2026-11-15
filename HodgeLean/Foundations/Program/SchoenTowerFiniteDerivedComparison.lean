import HodgeLean.Foundations.Program.SchoenTowerDiscreteSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
import HodgeLean.Foundations.Program.SchoenTowerConstantPullback

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.Program

def s2v_proper_finiteFibres_extEquiv {X Y : TopCat.{0}}
    [T2Space X] [LocallyCompactSpace X] (p : X ⟶ Y) (hp : IsProperMap p)
    (hfin : ∀ y : Y, Set.Finite {x : X | p x = y})
    (G : TopCat.Sheaf AddCommGrpCat.{0} Y) (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (n : ℕ) :
    Abelian.Ext ((TopCat.Sheaf.pullback AddCommGrpCat.{0} p).obj G) F n ≃+
      Abelian.Ext G ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj F) n := by
  let L := TopCat.Sheaf.pullback AddCommGrpCat.{0} p
  let R := TopCat.Sheaf.pushforward AddCommGrpCat.{0} p
  letI : PreservesFiniteLimits L := s3_pullback_preservesFiniteLimits p
  letI : PreservesFiniteColimits R :=
    s2v_proper_finiteFibres_pushforward_preservesFiniteColimits p hp hfin
  letI : L.Additive := Functor.additive_of_preserves_binary_products L
  letI : R.Additive := Functor.additive_of_preserves_binary_products R
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} p).extEquiv

def s2v_proper_finiteFibres_cohomologyEquiv {X Y : TopCat.{0}}
    [T2Space X] [LocallyCompactSpace X] (p : X ⟶ Y) (hp : IsProperMap p)
    (hfin : ∀ y : Y, Set.Finite {x : X | p x = y})
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    CategoryTheory.Sheaf.H F n ≃+
      CategoryTheory.Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj F) n := by
  let G := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of (ULift ℤ))
  let i := s2v_pullback_constantSheaf_iso p (AddCommGrpCat.of (ULift ℤ))
  let e : CategoryTheory.Sheaf.H F n ≃+
      Abelian.Ext ((TopCat.Sheaf.pullback AddCommGrpCat.{0} p).obj G) F n := {
    toFun := fun x => (Abelian.Ext.mk₀ i.hom).comp x (zero_add n)
    invFun := fun x => (Abelian.Ext.mk₀ i.inv).comp x (zero_add n)
    left_inv := by intro x; simp
    right_inv := by intro x; simp
    map_add' := by intro x z; exact Abelian.Ext.comp_add _ _ _ _ }
  exact e.trans (s2v_proper_finiteFibres_extEquiv p hp hfin G F n)

theorem s2v_proper_finiteFibres_cohomologyEquiv_naturality {X Y : TopCat.{0}}
    [T2Space X] [LocallyCompactSpace X] (p : X ⟶ Y) (hp : IsProperMap p)
    (hfin : ∀ y : Y, Set.Finite {x : X | p x = y})
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (g : F ⟶ G) (n : ℕ)
    (v : CategoryTheory.Sheaf.H F n) :
    s2v_proper_finiteFibres_cohomologyEquiv p hp hfin G n
        (CategoryTheory.Sheaf.H.map g n v) =
      CategoryTheory.Sheaf.H.map ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).map g) n
        (s2v_proper_finiteFibres_cohomologyEquiv p hp hfin F n v) := by
  let L := TopCat.Sheaf.pullback AddCommGrpCat.{0} p
  let R := TopCat.Sheaf.pushforward AddCommGrpCat.{0} p
  letI : PreservesFiniteLimits L := s3_pullback_preservesFiniteLimits p
  letI : PreservesFiniteColimits R :=
    s2v_proper_finiteFibres_pushforward_preservesFiniteColimits p hp hfin
  letI : L.Additive := Functor.additive_of_preserves_binary_products L
  letI : R.Additive := Functor.additive_of_preserves_binary_products R
  let i := s2v_pullback_constantSheaf_iso p (AddCommGrpCat.of (ULift ℤ))
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} p
  change adj.extEquiv ((Abelian.Ext.mk₀ i.hom).comp
      (v.comp (Abelian.Ext.mk₀ g) (add_zero n)) (zero_add n)) =
    (adj.extEquiv ((Abelian.Ext.mk₀ i.hom).comp v (zero_add n))).comp
      (Abelian.Ext.mk₀ (R.map g)) (add_zero n)
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero, adj.extEquiv_naturality_right₀]

end HodgeLean.Foundations.Program

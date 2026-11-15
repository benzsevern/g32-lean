import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! Extension of an actual null homotopy into a degreewise injective complex.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- An actual null homotopy on a degreewise subcomplex extends into injective terms, yielding a homotopic map that vanishes on that subcomplex.
Source: Weibel, An Introduction to Homological Algebra, section 2.3; extension through injective objects and the chain-homotopy formula.
HC no distance; AV milestone no distance.
-/
theorem exists_homotopic_vanishing_on_subcomplex {C : Type*} [Category* C] [Preadditive C]
    {ι : Type*} {c : ComplexShape ι} {B A I : HomologicalComplex C c}
    (i : B ⟶ A) (f : A ⟶ I) [∀ a, Mono (i.f a)] [∀ b, Injective (I.X b)]
    (h : Homotopy (i ≫ f) 0) :
    ∃ g : A ⟶ I, Nonempty (Homotopy f g) ∧ i ≫ g = 0 := by
  classical
  let h' (a b : ι) : A.X a ⟶ I.X b :=
    if hab : c.Rel b a then Injective.factorThru (h.hom a b) (i.f a) else 0
  have hz' (a b : ι) (hab : ¬ c.Rel b a) : h' a b = 0 := by
    simp only [h', dif_neg hab]
  have hlift (a b : ι) : i.f a ≫ h' a b = h.hom a b := by
    by_cases hab : c.Rel b a
    · simp only [h', dif_pos hab]
      exact Injective.comp_factorThru _ _
    · simp only [h', dif_neg hab, comp_zero, h.zero a b hab]
  let n := Homotopy.nullHomotopicMap h'
  have hin : i ≫ n = i ≫ f := by
    change i ≫ Homotopy.nullHomotopicMap h' = i ≫ f
    rw [Homotopy.comp_nullHomotopicMap]
    have hfam : (fun a b => i.f a ≫ h' a b) = h.hom := funext (fun a => funext (hlift a))
    rw [hfam]
    simpa only [sub_zero] using h.sub_eq_nullHomotopicMap.symm
  let g := f - n
  have heq : f - g = n := by dsimp [g]; abel
  have hn : Homotopy n 0 := Homotopy.nullHomotopy h' hz'
  refine ⟨g, ⟨Homotopy.equivSubZero.symm ((Homotopy.ofEq heq).trans hn)⟩, ?_⟩
  dsimp [g]
  rw [Preadditive.comp_sub, hin, sub_self]

#print axioms exists_homotopic_vanishing_on_subcomplex
end HodgeLean.Foundations.RationalHomologyManifold

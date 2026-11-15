import HodgeLean.Foundations.RationalHomologyManifold.InjectiveHomotopyExtension
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! Descent of an actual chain map after extension of its kernel null homotopy.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A map into degreewise injective terms descends up to its actual homotopy through a cokernel when its kernel restriction has a null homotopy.
Source: Weibel, An Introduction to Homological Algebra, section 2.3; injective extension followed by the cokernel universal property.
HC no distance; AV milestone no distance.
-/
theorem exists_homotopy_descent_of_cokernel {C : Type*} [Category* C] [Preadditive C]
    {ι : Type*} {c : ComplexShape ι} {B A D I : HomologicalComplex C c}
    (i : B ⟶ A) (r : A ⟶ D) (hir : i ≫ r = 0)
    (hr : IsColimit (CokernelCofork.ofπ r hir))
    (f : A ⟶ I) [∀ a, Mono (i.f a)] [∀ b, Injective (I.X b)]
    (h : Homotopy (i ≫ f) 0) :
    ∃ d : D ⟶ I, Nonempty (Homotopy f (r ≫ d)) := by
  obtain ⟨g, ⟨hg⟩, hig⟩ := exists_homotopic_vanishing_on_subcomplex i f h
  obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hr g hig
  exact ⟨d, ⟨hg.trans (Homotopy.ofEq hd.symm)⟩⟩

#print axioms exists_homotopy_descent_of_cokernel
end HodgeLean.Foundations.RationalHomologyManifold

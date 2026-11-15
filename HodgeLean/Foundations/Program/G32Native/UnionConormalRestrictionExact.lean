import HodgeLean.Foundations.AlgebraicGeometry.ConormalLocalIsomorphism
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Exactness under restriction to open subschemes -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Restriction of modules has the expected underlying abelian presheaf. -/
def unionConormalRestrictPresheafIso {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf X ≅
      Scheme.Modules.toPresheaf Y ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat).obj f.opensFunctor.op :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro M N g; rfl)

/-- Restriction to an open subscheme preserves finite limits of modules. -/
lemma unionConormal_restrict_preservesFiniteLimits {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  letI : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj f.opensFunctor.op) :=
    ⟨fun _ _ _ => inferInstance⟩
  letI : PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf X) :=
    preservesFiniteLimits_of_natIso (unionConormalRestrictPresheafIso f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (Scheme.Modules.restrictFunctor f) (Scheme.Modules.toPresheaf X)

/-- Open restriction preserves short exact module sequences. -/
lemma unionConormal_restrict_shortExact {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsOpenImmersion f] (S : ShortComplex Y.Modules)
    (hS : S.ShortExact) : (S.map (Scheme.Modules.restrictFunctor f)).ShortExact := by
  letI := unionConormal_restrict_preservesFiniteLimits f
  exact hS.map_of_exact _

end HodgeLean.Foundations.Program.G32Native

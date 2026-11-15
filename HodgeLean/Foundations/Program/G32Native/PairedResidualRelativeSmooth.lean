import HodgeLean.Foundations.Program.G32Native.PairedResidualRelativeCotangent
import HodgeLean.Foundations.Program.G32Native.PairedResidualSplitQuotient

/-! # A relative smoothness criterion for the actual differential pullback -/
noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- A retraction of the absolute differential pullback makes a formally smooth
absolute source formally smooth over the intermediate algebra.
Source: Stacks Project, Tags 00S2 and 00TI. -/
theorem residual_formallySmooth_of_differential_retraction
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T]
    (s : Ω[T⁄R] →ₗ[T] T ⊗[S] Ω[S⁄R])
    (hs : s.comp (KaehlerDifferential.mapBaseChange R S T) = LinearMap.id) :
    Algebra.FormallySmooth S T := by
  have hi : Function.Injective (KaehlerDifferential.mapBaseChange R S T) := by
    intro x y hxy
    have h := congrArg s hxy
    have hx := DFunLike.congr_fun hs x
    have hy := DFunLike.congr_fun hs y
    exact hx.symm.trans (h.trans hy)
  letI : Subsingleton (Algebra.H1Cotangent S T) :=
    residual_relative_h1_of_differential_injective R S T hi
  letI : Module.Projective T Ω[T⁄S] :=
    residual_projective_of_split_exact T (T ⊗[S] Ω[S⁄R]) Ω[T⁄R] Ω[T⁄S]
      (KaehlerDifferential.mapBaseChange R S T)
      (KaehlerDifferential.map R S T T) s hs
      (KaehlerDifferential.exact_mapBaseChange_map R S T)
      (KaehlerDifferential.map_surjective R S T)
  exact ⟨inferInstance, inferInstance⟩

#print axioms residual_formallySmooth_of_differential_retraction
end HodgeLean.Foundations.Program.G32Native

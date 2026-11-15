import HodgeLean.Foundations.Program.G32Native.PairedConormalCechNaturality
import HodgeLean.Foundations.Program.G32Native.PairedConormalCechInjective

/-! # The actual linear equivalence between global sections and zero cocycles -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program.G32Native
variable {R : Type*} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
    (K : X.OrderedAffineCover) (M : X.Modules)

/-- The map uses the actual restriction of the supplied global section on every intersection. -/
def conormalCechGlobalMap :
    (Scheme.Modules.toOModulePresheaf f M).obj ⊤ →ₗ[R]
      (Scheme.Modules.toOModulePresheaf f M).H0 K where
  toFun := conormalCechGlobalCocycle f K M
  map_add' x y := by
    apply Subtype.ext
    funext s
    exact map_add ((Scheme.Modules.toOModulePresheaf f M).res le_top) x y
  map_smul' r x := by
    apply Subtype.ext
    funext s
    exact map_smul ((Scheme.Modules.toOModulePresheaf f M).res le_top) r x

/-- Sheaf separatedness and gluing make the actual global restriction map bijective. -/
theorem conormalCechGlobalMap_bijective : Function.Bijective (conormalCechGlobalMap f K M) := by
  constructor
  · intro x y h
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ K.U ⊤
      (fun _ => homOfLE le_top) (by rw [K.iSup_eq_top])
    intro i
    have hv := congrArg (fun c => conormalCechVertexSection
      (Scheme.Modules.toOModulePresheaf f M) K c.val i) h
    exact (conormalCechGlobal_vertex f K M x i).symm.trans
      (hv.trans (conormalCechGlobal_vertex f K M y i))
  · intro c
    obtain ⟨x, hx⟩ := conormalCechGlobal_exists f K M c
    refine ⟨x, Subtype.ext ?_⟩
    apply conormalCechVertexSection_injective (Scheme.Modules.toOModulePresheaf f M) K
    funext i
    exact (conormalCechGlobal_vertex f K M x i).trans (hx i)

/-- Global sections and ordered zero cocycles carry the same original base-ring action. -/
def conormalCechGlobalEquiv :
    (Scheme.Modules.toOModulePresheaf f M).obj ⊤ ≃ₗ[R]
      (Scheme.Modules.toOModulePresheaf f M).H0 K :=
  LinearEquiv.ofBijective (conormalCechGlobalMap f K M) (conormalCechGlobalMap_bijective f K M)

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.PairedConormalCechGlobal

/-! # Naturality of the original sections in the ordered complex -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program.G32Native
variable {R : Type*} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
    (K : X.OrderedAffineCover)

/-- Extracting a vertex after restriction recovers the original section there. -/
theorem conormalCechGlobal_vertex (M : X.Modules) (x : Γ(M, ⊤)) (i : K.ι) :
    conormalCechVertexSection (Scheme.Modules.toOModulePresheaf f M) K
      (conormalCechGlobalCocycle f K M x).val i =
        M.presheaf.map (homOfLE (le_top : K.U i ≤ ⊤)).op x := by
  change (Scheme.Modules.toOModulePresheaf f M).res _
    ((Scheme.Modules.toOModulePresheaf f M).res _ x) = _
  exact OModulePresheaf.res_res (Scheme.Modules.toOModulePresheaf f M) _ _ x

/-- Vertex extraction commutes with the original morphism on sections. -/
theorem conormalCechVertex_naturality [IsSeparated f] {M N : X.Modules} (φ : M ⟶ N)
    (c : (Scheme.Modules.toOModulePresheaf f M).H0 K) (i : K.ι) :
    φ.app (K.U i)
      (conormalCechVertexSection (Scheme.Modules.toOModulePresheaf f M) K c.val i) =
    conormalCechVertexSection (Scheme.Modules.toOModulePresheaf f N) K
      (((Scheme.Modules.toOModulePresheafHom f φ).toAffHom.H0Map K) c).val i := by
  exact LinearMap.congr_fun ((Scheme.Modules.toOModulePresheafHom f φ).naturality
    (by rw [conormalCechVertex_inter K i])) (c.val (conormalCechVertex K i))

end HodgeLean.Foundations.Program.G32Native

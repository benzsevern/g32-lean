import HodgeLean.Foundations.Program.G32Native.TensorFrameCoefficients

/-! Restriction of coefficient descriptions of tensor sections. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
namespace HodgeLean.Foundations.Program

/-- Restricting a section written against a global frame restricts its coefficient. -/
theorem g32l4_tensor_section_restriction {X : Scheme.{0}} (F L : X.Modules)
    {V W : X.Opens} (hWV : W ≤ V) (t : Γ(F ⊗ L, ⊤)) (s : Γ(L, ⊤))
    (m : Γ(F, V))
    (h : (F ⊗ L).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t =
      tensorSections m (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s)) :
    (F ⊗ L).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t =
      tensorSections (F.presheaf.map (homOfLE hWV).op m)
        (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s) := by
  have res_res (M : X.Modules) (z : Γ(M, ⊤)) :
      M.presheaf.map (homOfLE hWV).op
        (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op z) =
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op z := by
    change (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      M.presheaf.map (homOfLE hWV).op).hom z = _
    rw [← Functor.map_comp]
    rfl
  rw [← res_res (F ⊗ L) t, h, map_tensorSections, res_res L s]

end HodgeLean.Foundations.Program

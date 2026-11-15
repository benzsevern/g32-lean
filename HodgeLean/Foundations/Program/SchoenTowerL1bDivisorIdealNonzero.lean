import HodgeLean.Foundations.Program.SchoenTowerL1bPrincipalNeighborhoods
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A nonzero section of an ideal on an integral scheme forces every local generator to have nonzero germ. -/
theorem s2v_l1b_divisor_ideal_generator_germ_ne_zero
    (X : Scheme) [IsIntegral X] (I : X.IdealSheafData)
    (W : X.affineOpens) [Nonempty W.1] (a : Γ(X, W))
    (haI : a ∈ I.ideal W) (ha : a ≠ 0)
    (x : X) (V : X.affineOpens) (hx : x ∈ V.1) (g : Γ(X, V))
    (hg : I.ideal V = Ideal.span {g}) :
    (X.presheaf.germ V.1 x hx).hom g ≠ 0 := by
  intro hzero
  have hgzero : g = 0 := germ_injective_of_isIntegral X x hx
    (hzero.trans (map_zero (X.presheaf.germ V.1 x hx).hom).symm)
  have hbotV : I.ideal V = ⊥ := by rw [hg, hgzero, Ideal.span_singleton_zero]
  have hxW : genericPoint X ∈ W.1 :=
    ((genericPoint_spec X).mem_open_set_iff W.1.isOpen).mpr
      (by simpa using ‹Nonempty W.1›)
  have hxV : genericPoint X ∈ V.1 :=
    ((genericPoint_spec X).mem_open_set_iff V.1.isOpen).mpr
      (by simpa using (show (V.1 : Set X).Nonempty from ⟨x, hx⟩))
  obtain ⟨O, hO, hxO, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X ∈ W.1 ⊓ V.1 from ⟨hxW, hxV⟩)
  letI : Nonempty O := ⟨⟨genericPoint X, hxO⟩⟩
  have hOW : O ≤ W.1 := fun _ hz => (hsub hz).1
  have hOV : O ≤ V.1 := fun _ hz => (hsub hz).2
  have hbotO : I.ideal ⟨O, hO⟩ = ⊥ := by
    rw [← I.map_ideal hOV, hbotV, Ideal.map_bot]
  have hmem : (X.presheaf.map (homOfLE hOW).op).hom a ∈ I.ideal ⟨O, hO⟩ := by
    rw [← I.map_ideal hOW]
    exact Ideal.mem_map_of_mem _ haI
  rw [hbotO, Ideal.mem_bot] at hmem
  exact ha (map_injective_of_isIntegral X (homOfLE hOW)
    (hmem.trans (map_zero (X.presheaf.map (homOfLE hOW).op).hom).symm))

end HodgeLean.Foundations.Program

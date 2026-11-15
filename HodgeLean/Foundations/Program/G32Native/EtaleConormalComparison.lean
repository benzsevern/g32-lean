import HodgeLean.Foundations.Program.G32Native.EtaleComponentNeighbourhood
import HodgeLean.Foundations.AlgebraicGeometry.ConormalBaseChange
import HodgeLean.Foundations.Program.G32Native.OpenConormalTransport

/-! # Component conormal comparison through the actual etale ambient map
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The original component conormal pulls back to the original lifted immersion conormal without a cartesian premise on the entire ambient scheme.
Source: Hartshorne, Algebraic Geometry, II.8, conormal flat base change;
EGA IV, 17.9.3 and 17.11.1, etale components.
HC no distance; AV milestone no distance. -/
theorem s2e_i1_etale_component_conormalIso
    {Q P W B : Over (Spec ↧ℂ)} (i : P ⟶ B) [IsClosedImmersion i.left]
    (β : W ⟶ B) [Etale β.left] (g : Q ⟶ P) [IsIso g.left]
    (j : Q ⟶ W) [IsClosedImmersion j.left] (h : g ≫ i = j ≫ β) :
    Nonempty (Conormal.sheaf j.left ≅
      (Scheme.Modules.pullback g.left).obj (Conormal.sheaf i.left)) := by
  have hleft : g.left ≫ i.left = j.left ≫ β.left := congrArg Over.Hom.left h
  obtain ⟨V, j', hj', hfac, hpb⟩ :=
    s2e_i1_etale_component_cartesian_neighbourhood i.left β.left g.left j.left hleft
  letI := hj'
  let E := Conormal.etaleBaseChangeIso i.left j' (V.ι ≫ β.left) g.left hpb
  exact ⟨(Classical.choice (i1_openConormalIso_aux j V.ι j' hfac)).symm ≪≫ E.symm⟩

#print axioms s2e_i1_etale_component_conormalIso

end HodgeLean.Foundations.Program.G32Native

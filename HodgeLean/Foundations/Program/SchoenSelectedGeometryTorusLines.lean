import HodgeLean.Foundations.Program.TorusAlgebraizationDefs

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Lattice homomorphisms send straight torus loops to the straight loops of their images. -/
theorem s0_torus_lattice_line_map
    {L M : Type} [AddCommGroup L] [AddCommGroup M]
    [Module.Finite ℤ L] [Module.Finite ℤ M]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) (F' : Submodule ℂ (ℂ ⊗[ℤ] M))
    (g : L →+ M) (hg : F ≤ F'.comap (b2_cplxMap g)) (l : L) (t : ℂ) :
    b2_torusHom F F' g hg (b2_torusCover L F (t • b5_lattice L F l)) =
      b2_torusCover M F' (t • b5_lattice M F' (g l)) := by
  change b2_torusHom F F' g hg
    (QuotientAddGroup.mk ((b2_coord _).symm (t • b2_coord _ (b2_latticeMap L F l)))) =
    QuotientAddGroup.mk ((b2_coord _).symm (t • b2_coord _ (b2_latticeMap M F' (g l))))
  simp only [LinearEquiv.map_smul, LinearEquiv.symm_apply_apply]
  change QuotientAddGroup.mk ((F.mapQ F' (b2_cplxMap g) hg)
    (t • b2_latticeMap L F l)) = QuotientAddGroup.mk (t • b2_latticeMap M F' (g l))
  rw [map_smul]
  rfl

#print axioms s0_torus_lattice_line_map
end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralChains

/-! Descent of integral cycle functionals through boundaries and torsion. -/
noncomputable section
open CategoryTheory
namespace HodgeLean.Foundations.Program

section Torsion
variable {R M V : Type} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V]
    [Module.IsTorsionFree R V]

theorem s4_c1a6_torsion_le_ker (f : M →ₗ[R] V) :
    Submodule.torsion R M ≤ LinearMap.ker f := by
  intro x hx
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
  have ha' : (a : R) • x = 0 := ha
  have h : (a : R) • f x = 0 := by rw [← map_smul, ha', map_zero]
  exact (smul_eq_zero.mp h).resolve_left (nonZeroDivisors.ne_zero a.property)

/-- Descent of a functional to the quotient by torsion. -/
def s4_c1a6_torsionDesc (f : M →ₗ[R] V) :
    (M ⧸ Submodule.torsion R M) →ₗ[R] V :=
  (Submodule.torsion R M).liftQ f (s4_c1a6_torsion_le_ker f)

theorem s4_c1a6_torsionDesc_mk (f : M →ₗ[R] V) (x : M) :
    s4_c1a6_torsionDesc f (Submodule.Quotient.mk x) = f x := rfl
end Torsion

variable {V : Type} [AddCommGroup V] [Module.IsTorsionFree ℤ V]

variable (S : ShortComplex (ModuleCat ℤ))

/-- A chain functional vanishing on boundaries induces a homology functional. -/
def s4_c1a6_boundaryDesc (f : S.X₂ →ₗ[ℤ] V)
    (hf : f.comp S.f.hom = 0) :
    S.homology →ₗ[ℤ] V :=
  (S.descHomology (S.iCycles ≫ ModuleCat.ofHom f) (by
      rw [← Category.assoc, S.toCycles_i]
      exact ModuleCat.hom_ext hf)).hom

/-- Descent through boundaries followed by descent through torsion. -/
def s4_c1a6_boundaryTorsionDesc (f : S.X₂ →ₗ[ℤ] V)
    (hf : f.comp S.f.hom = 0) :
    (S.homology ⧸ Submodule.torsion ℤ S.homology) →ₗ[ℤ] V :=
  (s4_c1a6_torsionDesc (s4_c1a6_boundaryDesc S f hf)).toAddMonoidHom.toIntLinearMap

theorem s4_c1a6_boundaryTorsionDesc_cycle (f : S.X₂ →ₗ[ℤ] V)
    (hf : f.comp S.f.hom = 0) (z : S.cycles) :
    s4_c1a6_boundaryTorsionDesc S f hf
      (Submodule.Quotient.mk (S.homologyπ z)) = f (S.iCycles z) := by
  change (S.homologyπ ≫ S.descHomology _ _) z = _
  rw [S.π_descHomology]
  rfl

theorem s4_c1a6_cycleClass_surjective (Y : CategoryTheory.Over
    (AlgebraicGeometry.Spec ↧ℂ)) : Function.Surjective (s4_c1a6_cycleClass Y) := by
  intro a
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((s4_c1a6_chains Y).homologyπ 1)).mp inferInstance h
  exact ⟨z, congrArg Submodule.Quotient.mk hz⟩

end HodgeLean.Foundations.Program

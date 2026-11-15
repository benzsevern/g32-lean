import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSupportHomology

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory AlgebraicTopology.Singular
variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
def b6m_cycleOfChain (K : ChainCategory R) (i : ℕ) (z : K.X i)
    (hz : (K.d i ((ComplexShape.down ℕ).next i)).hom z = 0) : K.cycles i :=
  (K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ z))
    ((ComplexShape.down ℕ).next i) rfl (by
      ext : 1
      apply LinearMap.ext_ring
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        LinearMap.toSpanSingleton_apply, one_smul, ModuleCat.hom_zero,
        LinearMap.zero_apply] using hz)).hom 1

set_option backward.isDefEq.respectTransparency false in
theorem b6m_cycleOfChain_inclusion (K : ChainCategory R) (i : ℕ) (z : K.X i)
    (hz : (K.d i ((ComplexShape.down ℕ).next i)).hom z = 0) :
    (K.iCycles i).hom (b6m_cycleOfChain R K i z hz) = z := by
  unfold b6m_cycleOfChain
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.liftCycles_i]
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]

set_option backward.isDefEq.respectTransparency false in
theorem b6m_homologyπ_zero_iff_boundary (K : ChainCategory R) (i : ℕ) (c : K.cycles i) :
    (K.homologyπ i).hom c = 0 ↔
      ∃ b : K.X (i + 1), (K.d (i + 1) i).hom b = (K.iCycles i).hom c := by
  let S := ShortComplex.mk (K.toCycles (i + 1) i) (K.homologyπ i)
    (K.toCycles_comp_homologyπ (i + 1) i)
  have hex : S.Exact := S.exact_of_g_is_cokernel
    (K.homologyIsCokernel (i + 1) i (by simp))
  constructor
  · intro hc
    obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff S).mp hex c hc
    refine ⟨b, ?_⟩
    have h := congrArg (K.iCycles i).hom hb
    exact (ConcreteCategory.congr_hom (K.toCycles_i (i + 1) i) b).symm.trans h
  · rintro ⟨b, hb⟩
    have hbc : (K.toCycles (i + 1) i).hom b = c := by
      apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
      exact (ConcreteCategory.congr_hom (K.toCycles_i (i + 1) i) b).trans hb
    rw [← hbc]
    exact congrArg (fun f => f.hom b) (K.toCycles_comp_homologyπ (i + 1) i)

theorem b6m_homologyπ_cyclesMap {K L : ChainCategory R} (f : K ⟶ L)
    (i : ℕ) (c : K.cycles i) :
    (L.homologyπ i).hom ((HomologicalComplex.cyclesMap f i).hom c) =
      (HomologicalComplex.homologyMap f i).hom ((K.homologyπ i).hom c) :=
  (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f i) c).symm

end HodgeLean.Foundations.Program

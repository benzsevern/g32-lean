import HodgeLean.Foundations.Program.SchoenTransferC1a5RelativeHelpers

/-! Naturality of relative excision squares and comparison transport.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- A commuting cube induces a commuting square on the actual relative chain maps.
Source: Hatcher §2.1, functoriality for pairs and excision. -/
lemma c1a5_relative_cube_naturality
    (F : SSet.{0} ⥤ ChainComplex (ModuleCat ℤ) ℕ)
    {A B C D A' B' C' D' : SSet.{0}}
    (f : A ⟶ B) (g : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (f' : A' ⟶ B') (g' : C' ⟶ D') (a' : A' ⟶ C') (b' : B' ⟶ D')
    (u : A ⟶ A') (v : B ⟶ B') (s : C ⟶ C') (t : D ⟶ D')
    (w : f ≫ b = a ≫ g) (w' : f' ≫ b' = a' ≫ g')
    (wf : f ≫ v = u ≫ f') (wg : g ≫ t = s ≫ g')
    (wa : a ≫ s = u ≫ a') (wb : b ≫ t = v ≫ b') :
    c1a5RelativeMap F f g a b w ≫ c1a5RelativeMap F g g' s t wg =
      c1a5RelativeMap F f f' u v wf ≫ c1a5RelativeMap F f' g' a' b' w' := by
  apply (cancel_epi (cokernel.π (F.map f))).1
  simp only [c1a5RelativeMap, cokernel.map, cokernel.π_desc_assoc,
    cokernel.π_desc, Category.assoc]
  rw [← Category.assoc, ← F.map_comp, wb, F.map_comp, Category.assoc]

/-- Two excision comparisons and a complement-pair comparison transport the ambient relative comparison.
Source: Hatcher §2.1, Theorem 2.20, the naturality diagram of relative excision. -/
lemma c1a5_relative_cube_comparison
    (F : SSet.{0} ⥤ ChainComplex (ModuleCat ℤ) ℕ)
    {A B C D A' B' C' D' : SSet.{0}}
    (f : A ⟶ B) (g : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (f' : A' ⟶ B') (g' : C' ⟶ D') (a' : A' ⟶ C') (b' : B' ⟶ D')
    (u : A ⟶ A') (v : B ⟶ B') (s : C ⟶ C') (t : D ⟶ D')
    (w : f ≫ b = a ≫ g) (w' : f' ≫ b' = a' ≫ g')
    (wf : f ≫ v = u ≫ f') (wg : g ≫ t = s ≫ g')
    (wa : a ≫ s = u ≫ a') (wb : b ≫ t = v ≫ b')
    (he : QuasiIso (c1a5RelativeMap F f g a b w))
    (he' : QuasiIso (c1a5RelativeMap F f' g' a' b' w'))
    (hv : QuasiIso (c1a5RelativeMap F f f' u v wf)) :
    QuasiIso (c1a5RelativeMap F g g' s t wg) := by
  have hh := c1a5_relative_cube_naturality F f g a b f' g' a' b' u v s t
    w w' wf wg wa wb
  have hc : QuasiIso
      (c1a5RelativeMap F f g a b w ≫ c1a5RelativeMap F g g' s t wg) := by
    rw [hh]
    have := he'
    have := hv
    infer_instance
  have := he
  have := hc
  exact quasiIso_of_comp_left (c1a5RelativeMap F f g a b w) _

end HodgeLean.Foundations.Program

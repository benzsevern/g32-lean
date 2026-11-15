import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineTransposeEpi

/-! # Transposition with specified associated-module presentations -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Specified associated-module presentations suffice for transposing an epimorphism. -/
lemma unionConormal_affineTranspose_epi_of_presentations
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (hφ : Function.Surjective φ.hom)
    {M : (Spec R).Modules} {N : (Spec S).Modules}
    (M₀ : ModuleCat R) (N₀ : ModuleCat S)
    (eM : M ≅ tilde M₀) (eN : N ≅ tilde N₀)
    (v : (Scheme.Modules.pullback (Spec.map φ)).obj M ⟶ N) [Epi v] :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _ v) := by
  let F := Scheme.Modules.pullback (Spec.map φ)
  let G := Scheme.Modules.pushforward (Spec.map φ)
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)
  let v' := F.map eM.inv ≫ v ≫ eN.hom
  haveI : Epi v' := by dsimp only [v']; infer_instance
  have ht := unionConormal_affineTranspose_epi R S φ hφ M₀ N₀ v'
  have he : adj.homEquiv _ _ v' = eM.inv ≫ adj.homEquiv _ _ v ≫ G.map eN.hom := by
    dsimp only [v']
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  haveI : Epi (eM.inv ≫ adj.homEquiv _ _ v ≫ G.map eN.hom) := by
    rw [← he]
    exact ht
  haveI : Epi (adj.homEquiv _ _ v ≫ G.map eN.hom) := epi_of_epi eM.inv _
  exact (epi_comp_iff_of_isIso _ (G.map eN.hom)).mp inferInstance

#print axioms unionConormal_affineTranspose_epi_of_presentations
end HodgeLean.Foundations.Program.G32Native

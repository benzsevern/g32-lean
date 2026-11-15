import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Finitely many actual stalk elements have simultaneous exact affine section representatives inside any prescribed neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.1–II.2. -/
theorem s2e_simultaneous_affine_germ_representatives
    (X : Scheme) (x : X) (U : X.Opens) (hxU : x ∈ U)
    {σ : Type*} [Finite σ] (r : σ → X.presheaf.stalk x) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : V ≤ U) (hxV : x ∈ V)
      (s : σ → Γ(X, V)), ∀ i, (X.presheaf.germ V x hxV).hom (s i) = r i := by
  classical
  choose W hxW s hs using fun i => X.presheaf.exists_germ_eq (r i)
  have hx : x ∈ U ⊓ ⨅ i, W i := by
    refine ⟨hxU, ?_⟩
    change x ∈ ((⨅ i, W i : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxW
  obtain ⟨V, hV, hxV, hsub⟩ := exists_isAffineOpen_mem_and_subset hx
  have hVW (i : σ) : V ≤ W i := hsub.trans (inf_le_right.trans (iInf_le W i))
  refine ⟨V, hV, hsub.trans inf_le_left, hxV,
    (fun i => (X.presheaf.map (homOfLE (hVW i)).op).hom (s i)), ?_⟩
  intro i
  change (X.presheaf.map (homOfLE (hVW i)).op ≫ X.presheaf.germ V x hxV).hom (s i) = r i
  rw [X.presheaf.germ_res]
  exact hs i

#print axioms s2e_simultaneous_affine_germ_representatives
end HodgeLean.Foundations.Program

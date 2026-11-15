import HodgeLean.Foundations.Program.SchoenCycleOrbitProductExtension
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Evaluation identifies the invariant algebra of transitive formal factors with the stabilizer-invariant algebra of the retained factor, preserving its actual value.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_transitive_product_invariant_algebra
    {k G ι : Type*} [CommRing k] [Group G] [MulAction G ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    (α : G →* ((∀ i, R i) ≃ₐ[k] (∀ i, R i))) (i₀ : ι)
    (htrans : ∀ i, ∃ g : G, g • i₀ = i)
    (hlocal : ∀ (g : G) (i : ι) (v w : ∀ j, R j),
      v i = w i → (α g v) (g • i) = (α g w) (g • i))
    (β : MulAction.stabilizer G i₀ → R i₀ →ₐ[k] R i₀)
    (hβ : ∀ (g : MulAction.stabilizer G i₀) (v : ∀ i, R i),
      (α g.val v) i₀ = β g (v i₀)) :
    ∃ E : (⨅ g : G, AlgHom.equalizer (α g).toAlgHom
        (AlgHom.id k (∀ i, R i)) : Subalgebra k (∀ i, R i)) ≃ₐ[k]
      (⨅ g : MulAction.stabilizer G i₀, AlgHom.equalizer (β g)
        (AlgHom.id k (R i₀)) : Subalgebra k (R i₀)),
      ∀ v, (E v).val = v.val i₀ := by
  classical
  let F : Subalgebra k (∀ i, R i) :=
    ⨅ g : G, AlgHom.equalizer (α g).toAlgHom (AlgHom.id k (∀ i, R i))
  let K : Subalgebra k (R i₀) :=
    ⨅ g, AlgHom.equalizer (β g) (AlgHom.id k (R i₀))
  have hF (v : F) (g : G) : α g v.val = v.val := by
    exact (Algebra.mem_iInf.mp v.property g)
  have hmem (v : F) : v.val i₀ ∈ K := by
    simp only [K, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    intro g
    rw [← hβ, hF]
  let ev : F →ₐ[k] K := ((Pi.evalAlgHom k R i₀).comp F.val).codRestrict K hmem
  have hinj : Function.Injective ev := by
    intro v w h
    apply Subtype.ext
    funext i
    obtain ⟨g, hg⟩ := htrans i
    have he : v.val i₀ = w.val i₀ := congrArg Subtype.val h
    have hh := hlocal g i₀ v.val w.val he
    rw [hg, hF, hF] at hh
    exact hh
  have hsurj : Function.Surjective ev := by
    intro v
    let z : ∀ i, R i := Function.update 0 i₀ v.val
    have hz₀ : z i₀ = v.val := Function.update_self _ _ _
    have hz (g : G) (hg : g • i₀ = i₀) : (α g z) i₀ = z i₀ := by
      let h : MulAction.stabilizer G i₀ := ⟨g, hg⟩
      have hv : β h v.val = v.val := Algebra.mem_iInf.mp v.property h
      rw [hβ h z, hz₀, hv]
    obtain ⟨w, hw, _⟩ := s2e_transitive_product_invariant_extension R α i₀ htrans hlocal z hz
    have hwF : w ∈ F := by
      simp only [F, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
      exact hw.1
    refine ⟨⟨w, hwF⟩, Subtype.ext ?_⟩
    exact hw.2.trans hz₀
  exact ⟨AlgEquiv.ofBijective ev ⟨hinj, hsurj⟩, fun _ => rfl⟩

end HodgeLean.Foundations.Program

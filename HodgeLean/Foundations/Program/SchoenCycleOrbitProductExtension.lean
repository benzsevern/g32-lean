import Mathlib.Algebra.Algebra.Pi
import Mathlib.GroupTheory.GroupAction.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A value invariant under one factor's stabilizer extends uniquely across a transitive orbit of algebra factors.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_transitive_product_invariant_extension
    {k G ι : Type*} [CommRing k] [Group G] [MulAction G ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    (α : G →* ((∀ i, R i) ≃ₐ[k] (∀ i, R i))) (i₀ : ι)
    (htrans : ∀ i, ∃ g : G, g • i₀ = i)
    (hlocal : ∀ (g : G) (i : ι) (v w : ∀ j, R j),
      v i = w i → (α g v) (g • i) = (α g w) (g • i))
    (z : ∀ i, R i)
    (hz : ∀ g : G, g • i₀ = i₀ → (α g z) i₀ = z i₀) :
    ∃! f : ∀ i, R i, (∀ g : G, α g f = f) ∧ f i₀ = z i₀ := by
  classical
  choose t ht using htrans
  have hmul (g h : G) (v : ∀ i, R i) : α (g * h) v = α g (α h v) := by
    rw [map_mul, AlgEquiv.mul_apply]
  have horbit (g h : G) (heq : g • i₀ = h • i₀) :
      (α g z) (g • i₀) = (α h z) (g • i₀) := by
    have hfix : (h⁻¹ * g) • i₀ = i₀ := by
      rw [mul_smul, heq, inv_smul_smul]
    have hh := hlocal h i₀ (α (h⁻¹ * g) z) z (hz _ hfix)
    rw [← hmul, mul_inv_cancel_left] at hh
    rw [← heq] at hh
    exact hh
  let f : ∀ i, R i := fun i => α (t i) z i
  have hf (g : G) : α g f = f := by
    funext i
    let j := g⁻¹ • i
    have hgj : g • j = i := smul_inv_smul g i
    have hbase : f j = (α (t j) z) j := rfl
    have he := hlocal g j f (α (t j) z) hbase
    rw [hgj, ← hmul] at he
    have hti : (g * t j) • i₀ = i := by rw [mul_smul, ht, hgj]
    have ho := horbit (g * t j) (t i) (hti.trans (ht i).symm)
    rw [hti] at ho
    exact he.trans ho
  have hf₀ : f i₀ = z i₀ := by
    exact hz (t i₀) (ht i₀)
  refine ⟨f, ⟨hf, hf₀⟩, ?_⟩
  intro w hw
  funext i
  have he := hlocal (t i) i₀ w f (hw.2.trans hf₀.symm)
  rw [ht, hw.1, hf] at he
  exact he

end HodgeLean.Foundations.Program

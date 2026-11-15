module

public import HodgeLean.Foundations.Program.RelativeTorusIdempotentProofs

/-! # Track B2, idempotents of a lattice (FROZEN SPEC)

The two lattice statements of track B2 that need only Mathlib: the kernel of an idempotent
`e : Λ → Λ` is the image of `1 - e`, and for an idempotent symmetric for a bilinear form `Q` the
images of `e` and `1 - e` are `Q`-orthogonal. They are used by `RelativeTorusKernel.lean` (the
kernel of a flat idempotent is the image of `1 - e`) and stated here so that they elaborate with
Mathlib alone. Each theorem is the matching `_aux` theorem of `RelativeTorusIdempotentProofs.lean`.

Not claimed: anything about tori, Hodge structures or families. HC no distance; AV milestone no
distance.
-/

public section

namespace HodgeLean.Foundations.Program

variable {Λ : Type*} [AddCommGroup Λ]

/-- **The kernel of an idempotent is the image of `1 - e`.**
Source: Bourbaki, *Algèbre*, ch. II, §1.9 (projectors); Birkenhake–Lange, §5.3. -/
theorem b2_ker_eq_range (e : Λ →+ Λ) (he : e.comp e = e) :
    e.ker = (AddMonoidHom.id Λ - e).range :=
  b2_ker_eq_range_aux e he

example : (AddMonoidHom.id Λ).ker = (AddMonoidHom.id Λ - AddMonoidHom.id Λ).range :=
  b2_ker_eq_range _ rfl

/-- **Orthogonality for a symmetric idempotent.** If `e` is idempotent and symmetric for `Q`
(`Q(e x, y) = Q(x, e y)`), then `Q(e(Λ), (1 - e)(Λ)) = 0`.
Source: Birkenhake–Lange, §5.3 (symmetric idempotents and complementary abelian
subvarieties). -/
theorem b2_orthogonal_of_symm (Q : LinearMap.BilinForm ℤ Λ) (e : Λ →+ Λ)
    (he : e.comp e = e) (hQ : ∀ x y, Q (e x) y = Q x (e y)) :
    ∀ x ∈ e.range, ∀ y ∈ (AddMonoidHom.id Λ - e).range, Q x y = 0 :=
  b2_orthogonal_of_symm_aux Q e he hQ

example (Q : LinearMap.BilinForm ℤ Λ) (x : Λ) (y : Λ)
    (hy : y ∈ (AddMonoidHom.id Λ - AddMonoidHom.id Λ).range) : Q x y = 0 :=
  b2_orthogonal_of_symm Q _ rfl (fun _ _ ↦ rfl) x ⟨x, rfl⟩ y hy

end HodgeLean.Foundations.Program

end

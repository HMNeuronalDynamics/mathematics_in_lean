import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  split
  · intro h x xs
    exact h ⟨x, xs, rfl⟩
  · rintro h y ⟨x, xs, rfl⟩
    exact h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x hx
  rcases hx with ⟨y, ys, rfl⟩
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact hx

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y hy
  rcases h y with ⟨x, rfl⟩
  use x
  exact ⟨hy, rfl⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y hy
  rcases hy with ⟨x, xs, rfl⟩
  use x
  exact ⟨h xs, rfl⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hx
  exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  simp only [mem_preimage, mem_union_eq]
  rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y hy
  rcases hy with ⟨x, ⟨xs, xt⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, ⟨x, xt, rfl⟩⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x, xs, rfl⟩, ⟨x', xt, heq⟩⟩
  have : x = x' := h heq
  subst this
  use x, ⟨xs, xt⟩
  rfl

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, xs, rfl⟩, ynt⟩
  use x
  constructor
  · exact ⟨xs, fun hxt => ynt ⟨x, hxt, rfl⟩⟩
  rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨hx, hnx⟩
  constructor
  · exact hx
  · intro hxv
    exact hnx hxv

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  simp only [mem_inter_iff, mem_image, mem_preimage]
  constructor
  · rintro ⟨⟨x, xs, rfl⟩, yv⟩
    exact ⟨x, ⟨xs, yv⟩, rfl⟩
  rintro ⟨x, ⟨xs, xv⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, xv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, xu⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, xu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨xs, xu⟩
  exact ⟨⟨x, xs, rfl⟩, xu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x hx
  cases hx
  · left
    use x, hx
  right
  exact hx

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp only [mem_image, mem_iUnion]
  constructor
  · rintro ⟨x, ⟨i, xi⟩, rfl⟩
    exact ⟨i, ⟨x, xi, rfl⟩⟩
  rintro ⟨i, ⟨x, xi, rfl⟩⟩
  exact ⟨x, ⟨i, xi⟩, rfl⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y hy
  simp only [mem_image, mem_iInter] at *
  rintro i
  rcases hy with ⟨x, h, rfl⟩
  exact ⟨x, h i, rfl⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y hy
  simp only [mem_image, mem_iInter] at *
  rcases hy i with ⟨x, hxi, rfl⟩
  use x
  intro j
  specialize hy j
  rcases hy with ⟨x', hx'j, hx'eq⟩
  have : x = x' := injf hx'eq
  rwa [← this]

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp only [mem_preimage, mem_iUnion]
  rfl

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp only [mem_preimage, mem_iInter]
  rfl

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]

example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro e
  rw [sqrt_eq_iff_sq_eq xnonneg ynonneg] at e
  exact e

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro e
  rw [sq_eq_sq x y] at e
  cases e
  · assumption
  · exfalso
    linarith

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  simp only [mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨x, xnonneg, rfl⟩
    apply sqrt_nonneg
  intro ynonneg
  use y ^ 2
  constructor
  · apply pow_two_nonneg
  rw [sqrt_sqr ynonneg]

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  simp only [mem_range, mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    apply pow_two_nonneg
  intro ynonneg
  use sqrt y
  rw [sqrt_sqr ynonneg]

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro injf
    intro x
    rw [inverse, dif_pos]
    · exact Classical.choose_spec ⟨x, rfl⟩
    use x
  intro linv
  intros x y hxy
  have : inverse f (f x) = inverse f (f y) := by rw [hxy]
  rw [linv x, linv y] at this
  exact this

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro surjf
    intro y
    rw [inverse, dif_pos]
    · exact Classical.choose_spec (surjf y)
    exact surjf y
  intro rinv
  intro y
  use inverse f y
  exact rinv y

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h]
  contradiction

-- COMMENTS: TODO: improve this
end

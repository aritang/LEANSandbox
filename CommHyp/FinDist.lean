import Mathlib

/-!
# Finite probability distributions

`μ : FinDist α` is a weight `μ.w a ≥ 0` on each `a : α` (finite), summing to 1.

Five operations, each defined by its weights:

* `pure a` — point mass `δₐ`: `(pure a).w b = if b = a then 1 else 0`
* `map f μ` — pushforward `f₊μ`: `(map f μ).w b = ∑ a with f a = b, μ.w a`
* `bind μ f` — mixture, with `f a` read as `P(· ∣ a)`:
  `(bind μ f).w b = ∑ a, μ.w a * (f a).w b`   (law of total probability)
* `pi μ` — independent product `⊗ᵢ μᵢ`: `(pi μ).w s = ∏ i, (μ i).w (s i)`
* `prod μ ν` — independent pair `μ ⊗ ν`: `(prod μ ν).w (a, b) = μ.w a * ν.w b`

**Convention:** explicit code first, then a `Short form:` comment. Explicit means
binder types written out and functions called by full name (`FinDist.bind μ f`,
not `μ.bind f`). Structure fields use dot notation in both forms (`μ.w`).
-/

open Classical
noncomputable section

/-- `FinDist` is a structure that takes a finite type `α` and bundles a weight
function `w : α → ℝ` with proofs that `w ≥ 0` and `∑ w = 1`.

`@[ext]` generates `FinDist.ext : μ.w = ν.w → μ = ν` (equal weights ⇒ equal
distributions; the proof fields don't matter). The `ext` tactic uses it to turn
a goal `μ = ν` into `μ.w b = ν.w b` for every `b`, as in the laws below. -/
@[ext]
structure FinDist (α : Type) [Fintype α] where
  w : α → ℝ
  nonneg : ∀ a : α, 0 ≤ w a
  sum_one : ∑ a : α, w a = 1

namespace FinDist

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-- `pure` is a function that takes a point `a : α` and returns the point mass
at `a`, a distribution `FinDist α`. -/
def pure (a : α) : FinDist α where
  w := fun (b : α) => if b = a then 1 else 0
  nonneg := fun (b : α) => by
    show (0 : ℝ) ≤ if b = a then 1 else 0
    split_ifs <;> norm_num
  sum_one := by simp

/-- `bind` is a function that takes a distribution `μ : FinDist α` and a
conditional distribution `f : α → FinDist β` (`f a = P(· ∣ a)`) and returns
the mixture `FinDist β`: `P(b) = ∑ₐ μ(a) · P(b ∣ a)`. -/
def bind (μ : FinDist α) (f : α → FinDist β) : FinDist β where
  w := fun (b : β) => ∑ a : α, μ.w a * (f a).w b
  nonneg := fun (b : β) => by
    have h1 : ∀ a : α, 0 ≤ μ.w a := μ.nonneg
    have h2 : ∀ a : α, 0 ≤ (f a).w b := fun (a : α) => (f a).nonneg b
    have h3 : ∀ a : α, 0 ≤ μ.w a * (f a).w b :=
      fun (a : α) => mul_nonneg (h1 a) (h2 a)
    exact Finset.sum_nonneg (fun (a : α) (_ : a ∈ Finset.univ) => h3 a)
  sum_one := by
    show ∑ b : β, ∑ a : α, μ.w a * (f a).w b =1
    rw [Finset.sum_comm]
    have h : ∀ a : α, ∑ b : β, μ.w a * (f a).w b = μ.w a := fun (a : α) => by
      rw [← Finset.mul_sum, (f a).sum_one, mul_one]
    simp only [h]
    exact μ.sum_one

/-- `map` is a function that takes `f : α → β` and `μ : FinDist α` and returns
the pushforward `f₊μ : FinDist β`: `b : β, P(b) = ∑_{a : f a = b} μ(a)`. -/
def map (f : α → β) (μ : FinDist α) : FinDist β :=
  FinDist.bind μ (fun (a : α) => FinDist.pure (f a))

/-- `E` is a function that takes `μ : FinDist α` and `g : α → ℝ` and returns
the expectation `∑ₐ μ(a) · g(a) : ℝ`. -/
def E (μ : FinDist α) (g : α → ℝ) : ℝ :=
  ∑ a : α, μ.w a * g a

/-- `pi` is a function that takes one distribution `μ i : FinDist (X i)` per
`i : ι` and returns their independent product, a distribution on profiles
`FinDist (∀ i, X i)`: `P(s) = ∏ᵢ μᵢ(sᵢ)`. -/
def pi {ι : Type} [Fintype ι] {X : ι → Type} [∀ i : ι, Fintype (X i)]
    (μ : ∀ i : ι, FinDist (X i)) : FinDist (∀ i : ι, X i) where
  w := fun (s : ∀ i : ι, X i) => ∏ i : ι, (μ i).w (s i)
  nonneg := fun (s : ∀ i : ι, X i) => by
    have h : ∀ i : ι, 0 ≤ (μ i).w (s i) := fun (i : ι) => (μ i).nonneg (s i)
    exact Finset.prod_nonneg (fun (i : ι) (_ : i ∈ Finset.univ) => h i)
  sum_one := by
    show ∑ s : (∀ i : ι, X i), ∏ i : ι, (μ i).w (s i) = 1
    rw [← Fintype.prod_sum]
    have h : ∀ i : ι, ∑ x : X i, (μ i).w x = 1 := fun (i : ι) => (μ i).sum_one
    simp only [h]
    exact Finset.prod_const_one

/-- `prod` is a function that takes `μ : FinDist α` and `ν : FinDist β` and returns
their independent product, a distribution on pairs `FinDist (α × β)`:
`P(a, b) = μ(a) · ν(b)`. -/
def prod (μ : FinDist α) (ν : FinDist β) : FinDist (α × β) where
  w := fun (p : α × β) => μ.w p.1 * ν.w p.2
  nonneg := fun (p : α × β) => mul_nonneg (μ.nonneg p.1) (ν.nonneg p.2)
  sum_one := by
    show ∑ p : α × β, μ.w p.1 * ν.w p.2 = 1
    rw [Fintype.sum_prod_type]
    have h : ∀ a : α, ∑ b : β, μ.w a * ν.w b = μ.w a := fun (a : α) => by
      rw [← Finset.mul_sum, ν.sum_one, mul_one]
    simp only [h]
    exact μ.sum_one

end FinDist

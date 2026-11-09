import Mathlib

/-!
# Finite probability distributions

`FinDist α` is a probability distribution on a finite type `α`, with operations `pure`, `bind`, `map`, `E`, `pi`, `prod`, and the laws `pure_bind`, `map_id'`, `pi_pure`.

**Convention:** explicit code first, then a `Short form:` comment. Explicit means binder types written out and functions called by full name (`FinDist.bind μ f`, not `μ.bind f`). Structure fields use dot notation in both forms (`μ.w`).
-/

open Classical
noncomputable section

/-- `FinDist α` is a probability distribution on `α`: `w a` is the probability of `a`.

`@[ext]`: two distributions with the same `w` are equal. -/
@[ext]
structure FinDist (α : Type) [Fintype α] where
  w : α → ℝ
  nonneg : ∀ a : α, 0 ≤ w a
  sum_one : ∑ a : α, w a = 1

namespace FinDist

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-- `pure a` returns the point distribution at `a`. -/
def pure (a : α) : FinDist α where
  w := fun (b : α) => if b = a then 1 else 0
  nonneg := fun (b : α) => by
    show (0 : ℝ) ≤ if b = a then 1 else 0
    split_ifs <;> norm_num
  sum_one := by simp

/-- `bind μ f`, for `μ : FinDist α` and `f : α → FinDist β`, returns the distribution of `b` when `a` is drawn from `μ` and then `b` from `f a`. -/
def bind (μ : FinDist α) (f : α → FinDist β) : FinDist β where
  w := fun (b : β) => ∑ a : α, μ.w a * (f a).w b
  nonneg := fun (b : β) => by
    have h1 : ∀ a : α, 0 ≤ μ.w a := μ.nonneg
    have h2 : ∀ a : α, 0 ≤ (f a).w b := fun (a : α) => (f a).nonneg b
    have h3 : ∀ a : α, 0 ≤ μ.w a * (f a).w b := fun (a : α) => mul_nonneg (h1 a) (h2 a)
    exact Finset.sum_nonneg (fun (a : α) (_ : a ∈ Finset.univ) => h3 a)
  sum_one := by
    show ∑ b : β, ∑ a : α, μ.w a * (f a).w b = 1
    rw [Finset.sum_comm]
    have h : ∀ a : α, ∑ b : β, μ.w a * (f a).w b = μ.w a := fun (a : α) => by
      rw [← Finset.mul_sum, (f a).sum_one, mul_one]
    simp only [h]
    exact μ.sum_one

/-- `f♯ μ` is `bind μ f`: draw `a` from `μ`, then draw from `f a`. -/
notation:max f:max "♯" μ:max => FinDist.bind μ f

/-- `map f μ`, for `f : α → β` and `μ : FinDist α`, returns the distribution of `f a` when `a` is drawn from `μ`. -/
def map (f : α → β) (μ : FinDist α) : FinDist β :=
  FinDist.bind μ (fun (a : α) => FinDist.pure (f a))

/-- `f ₊ μ` is `map f μ`: the distribution of `f a` when `a` is drawn from `μ`. -/
notation:max f:max " ₊ " μ:max => FinDist.map f μ


/-- `E μ g` returns the expected value of `g : α → ℝ` under `μ`. -/
def E (μ : FinDist α) (g : α → ℝ) : ℝ :=
  ∑ a : α, μ.w a * g a

/-- `pi μ` returns the independent product of the distributions `μ i`, a distribution on profiles `∀ i, X i`. -/
def pi {ι : Type} [Fintype ι] {X : ι → Type} [∀ i : ι, Fintype (X i)] (μ : ∀ i : ι, FinDist (X i)) : FinDist (∀ i : ι, X i) where
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

/-- `prod μ ν` returns the independent product of `μ` and `ν`, a distribution on pairs `α × β`. -/
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

/-!
## Monad laws
-/



/--
`bind_assoc`

Input:
μ : FinDist α;
f : α → FinDist β;
g : β → FinDist γ;

Proves:
(μ.bind f).bind g = μ.bind (fun a ↦ (f a).bind g)
-/
lemma bind_assoc (μ : FinDist α) (f : α → FinDist β) (g : β → FinDist γ) : FinDist.bind (FinDist.bind μ f) g = FinDist.bind μ (fun (a : α) => FinDist.bind (f a) g) := by
  ext c
  simp only [FinDist.bind, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- lemma `bind_comm`: drawing from two independent distributions in either order gives the same result. -/
lemma bind_comm (μ : FinDist α) (ν : FinDist β) (h : α → β → FinDist γ) : FinDist.bind μ (fun (a : α) => FinDist.bind ν (fun (b : β) => h a b)) = FinDist.bind ν (fun (b : β) => FinDist.bind μ (fun (a : α) => h a b)) := by
  -- Step 1: compare the weight of each point `c`.
  ext c
  -- Step 2: unfold `bind` into sums and move the outer weight inside the inner sum.
  simp only [FinDist.bind, Finset.mul_sum]
  -- Step 3: swap the sum over `a` and the sum over `b`.
  rw [Finset.sum_comm]
  -- Step 4: reorder the products so the two sides match.
  simp only [mul_left_comm]

/-- lemma `pure_bind`: for a point `a : α` and `f : α → FinDist β`, `bind (pure a) f = f a`. -/
lemma pure_bind (a : α) (f : α → FinDist β) : FinDist.bind (FinDist.pure a) f = f a := by
  -- Two distributions are equal if they give every point the same weight.
  ext b
  simp [FinDist.bind, FinDist.pure]

/-- lemma `map_id'`: mapping `μ` by the identity function gives `μ`. -/
lemma map_id' (μ : FinDist α) : FinDist.map (fun (a : α) => a) μ = μ := by
  ext b
  simp [FinDist.map, FinDist.bind, FinDist.pure]

/-- lemma `pi_pure`: the product of the point distributions at `x i` is the point distribution at `x`. -/
lemma pi_pure {ι : Type} [Fintype ι] {X : ι → Type} [∀ i : ι, Fintype (X i)] (x : ∀ i : ι, X i) : FinDist.pi (fun (i : ι) => FinDist.pure (x i)) = FinDist.pure x := by
  ext b
  simp [FinDist.pi, FinDist.pure]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

/-- lemma `bind_map`:
- f : α → β
- μ : FinDist α
- g : β → FinDist γ

⊢ (map f μ).bind g = μ.bind fun a ↦ g (f a)
-/
lemma bind_map (f : α → β) (μ : FinDist α) (g : β → FinDist γ) : FinDist.bind (FinDist.map f μ) g = FinDist.bind μ (g ∘ f) := by
  sorry

/-- lemma `map_bind`: mapping the result of a bind is the same as mapping inside each branch of the bind. -/
lemma map_bind (f : β → γ) (μ : FinDist α) (g : α → FinDist β) : FinDist.map f (FinDist.bind μ g) = FinDist.bind μ (fun (a : α) => FinDist.map f (g a)) := by
  sorry

/-- lemma `map_map`: mapping twice is the same as mapping once by the composed function. -/
lemma map_map (f : α → β) (g : β → γ) (μ : FinDist α) : FinDist.map g (FinDist.map f μ) = FinDist.map (fun (a : α) => g (f a)) μ := by
  sorry

/-- lemma `prod_bind`: drawing a pair from an independent product is the same as drawing the first coordinate and then the second. -/
lemma prod_bind (μ : FinDist α) (ν : FinDist β) (h : α × β → FinDist γ) : FinDist.bind (FinDist.prod μ ν) h = FinDist.bind μ (fun (a : α) => FinDist.bind ν (fun (b : β) => h (a, b))) := by
  sorry

/-- lemma `pi_update_bind`: drawing a profile whose `i`-th coordinate comes from `ν` is the same as drawing `x` from `ν`, drawing a profile from the original product, and replacing its `i`-th coordinate by `x`. -/
lemma pi_update_bind {ι : Type} [Fintype ι] {X : ι → Type} [∀ i : ι, Fintype (X i)] (μ : ∀ i : ι, FinDist (X i)) (i : ι) (ν : FinDist (X i)) (F : (∀ j : ι, X j) → FinDist γ) : FinDist.bind (FinDist.pi (Function.update μ i ν)) F = FinDist.bind ν (fun (x : X i) => FinDist.bind (FinDist.pi μ) (fun (s : ∀ j : ι, X j) => F (Function.update s i x))) := by
  sorry

end FinDist

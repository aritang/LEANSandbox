import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.NormNum.Basic

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

/-- `μ >>= f`, for `μ : FinDist α` and `f : α → FinDist β`, is `bind μ f : FinDist β`. -/
notation:55 μ:55 " >>= " f:56 => FinDist.bind μ f

/-- `g ⊚ f`, for `f : α → FinDist β` and `g : β → FinDist γ`, is the function `α → FinDist γ` that sends `a` to `f a >>= g`. -/
notation:60 g:61 " ⊚ " f:61 => fun a => FinDist.bind (f a) g

/-- `map f μ`, for `f : α → β` and `μ : FinDist α`, returns the distribution of `f a` when `a` is drawn from `μ`. -/
def map (f : α → β) (μ : FinDist α) : FinDist β :=
  FinDist.bind μ (fun (a : α) => FinDist.pure (f a))

/-- `f <$> μ`, for `f : α → β` and `μ : FinDist α`, is `map f μ : FinDist β`. -/
notation:100 f:101 " <$> " μ:100 => FinDist.map f μ


/-- `E μ g` returns the expected value of `g : α → ℝ` under `μ`. -/
def E (μ : FinDist α) (g : α → ℝ) : ℝ :=
  ∑ a : α, μ.w a * g a

/-- `𝔼[g ; μ]`, for `g : α → ℝ` and `μ : FinDist α`, is `E μ g : ℝ`. -/
notation "𝔼[" g " ; " μ "]" => FinDist.E μ g

/-- `pi μ` returns the independent product of the distributions `μ i`, a distribution on profiles `∀ i, X i`. -/
def pi
    {ι : Type} [Fintype ι] {X : ι → Type} [∀ i : ι, Fintype (X i)]
    (μ : ∀ i : ι, FinDist (X i)) :
    FinDist (∀ i : ι, X i) where
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

/-- `⨂ μ`, for `μ : ∀ i, FinDist (X i)`, is `pi μ : FinDist (∀ i, X i)`. -/
notation "⨂ " μ:max => FinDist.pi μ

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

/-- `μ ⊗ ν`, for `μ : FinDist α` and `ν : FinDist β`, is `prod μ ν : FinDist (α × β)`. -/
notation:70 μ:70 " ⊗ " ν:71 => FinDist.prod μ ν



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
(μ >>= f) >>= g = μ >>= (fun a ↦ f a >>= g)
-/
lemma bind_assoc
    (μ : FinDist α)
    (f : α → FinDist β)
    (g : β → FinDist γ) :
    (μ >>= f) >>= g = μ >>= (g ⊚ f) := by
  ext c
  simp only [FinDist.bind, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- lemma `bind_comm`:
- μ : FinDist α
- ν : FinDist β
- h : α → β → FinDist γ

⊢ μ >>= (fun a ↦ ν >>= (fun b ↦ h a b)) = ν >>= (fun b ↦ μ >>= (fun a ↦ h a b))
-/
lemma bind_comm
    (μ : FinDist α)
    (ν : FinDist β)
    (h : α → β → FinDist γ) :
    μ >>= (fun (a : α) => ν >>= (fun (b : β) => h a b))
      = ν >>= (fun (b : β) => μ >>= (fun (a : α) => h a b)) := by
  -- Step 1: compare the weight of each point `c`.
  ext c
  -- Step 2: unfold `bind` into sums and move the outer weight inside the inner sum.
  simp only [FinDist.bind, Finset.mul_sum]
  -- Step 3: swap the sum over `a` and the sum over `b`.
  rw [Finset.sum_comm]
  -- Step 4: reorder the products so the two sides match.
  simp only [mul_left_comm]

/-- lemma `pure_bind`: for a point `a : α` and `f : α → FinDist β`, `pure a >>= f = f a`. -/
lemma pure_bind (a : α) (f : α → FinDist β) : FinDist.pure a >>= f = f a := by
  -- Two distributions are equal if they give every point the same weight.
  ext b
  simp [FinDist.bind, FinDist.pure]

/-- lemma `map_id'`: mapping `μ` by the identity function gives `μ`. -/
lemma map_id' (μ : FinDist α) : (fun (a : α) => a) <$> μ = μ := by
  ext b
  simp [FinDist.map, FinDist.bind, FinDist.pure]

/-- lemma `pi_pure`: the product of the point distributions at `x i` is the point distribution at `x`. -/
lemma pi_pure
    {ι : Type} [Fintype ι] {X : ι → Type} [∀ i : ι, Fintype (X i)]
    (x : ∀ i : ι, X i) :
    FinDist.pi (fun (i : ι) => FinDist.pure (x i)) = FinDist.pure x := by
  ext b
  simp [FinDist.pi, FinDist.pure]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

/-- lemma `bind_map`:
- f : α → β
- μ : FinDist α
- g : β → FinDist γ

⊢ (f <$> μ) >>= g = μ >>= (g ∘ f)
-/
lemma bind_map
    (f : α → β)
    (μ : FinDist α)
    (g : β → FinDist γ) :
    (f <$> μ) >>= g = μ >>= (g ∘ f) := by
  rw [FinDist.map, FinDist.bind_assoc]
  simp only [FinDist.pure_bind]
  rfl

/-- lemma `map_bind`:
- f : β → γ
- μ : FinDist α
- g : α → FinDist β

⊢ f <$> (μ >>= g) = μ >>= (fun a ↦ f <$> g a)
-/
lemma map_bind
    (f : β → γ)
    (μ : FinDist α)
    (g : α → FinDist β) :
    f <$> (μ >>= g) = μ >>= (fun (a : α) => f <$> g a) := by
  -- Step 1: unfold the outer `map` into a `bind` with `pure ∘ f`.
  rw [FinDist.map]
  -- Step 2: reassociate the two binds.
  rw [FinDist.bind_assoc]
  -- Step 3: both sides now agree by unfolding `map` (definitional equality).
  rfl

/-- lemma `map_map`:
- f : α → β
- g : β → γ
- μ : FinDist α

⊢ g <$> (f <$> μ) = (fun a ↦ g (f a)) <$> μ
-/
lemma map_map
    (f : α → β)
    (g : β → γ)
    (μ : FinDist α) :
    g <$> (f <$> μ) = (fun (a : α) => g (f a)) <$> μ := by
  -- Step 1: unfold only the outer `map g` into a `bind` with `pure ∘ g`.
  rw [FinDist.map]
  -- Step 2: the goal is now `(f <$> μ) >>= (fun b ↦ pure (g b)) = ...`; apply `bind_map`.
  rw [FinDist.bind_map]
  -- Step 3: both sides are `μ >>= (fun a ↦ pure (g (f a)))` after unfolding `∘` and `map`.
  rfl

/-- lemma `prod_bind`:
- μ : FinDist α
- ν : FinDist β
- h : α × β → FinDist γ

⊢ (μ ⊗ ν) >>= h = μ >>= (fun a ↦ ν >>= (fun b ↦ h (a, b)))
-/
lemma prod_bind
    (μ : FinDist α)
    (ν : FinDist β)
    (h : α × β → FinDist γ) :
    (μ ⊗ ν) >>= h
      = μ >>= (fun (a : α) => ν >>= (fun (b : β) => h (a, b))) := by
  -- Step 1: compare the weight of each point `c`.
  ext c
  -- Step 2: unfold every `bind` and `prod` (on both sides) into sums.
  simp only [FinDist.bind, FinDist.prod]
  -- Step 3: split the sum over pairs `p : α × β` into a double sum over `a`, then `b`.
  rw [Fintype.sum_prod_type]
  -- Step 4: push `μ.w a` inside the inner sum on the right, and regroup the products.
  simp only [Finset.mul_sum, mul_assoc]


/-!
### Bookkeeping for `pi_update_bind`

Notation used below, for a player `i`:
- `r : ∀ j : {j // j ≠ i}, X j` is the actions of everyone except `i` ("`s_{-i}`").
- `(Equiv.piSplitAt i X).symm (x, r)` is the full profile with `x` for player `i` and `r` for everyone else ("`(x, s_{-i})`").
-/

/-- `_sum_pi_split` (bookkeeping): a sum over profiles `s` is a double sum over `x = s_i` and `r = s_{-i}`.

⊢ ∑ s, f s = ∑ x, ∑ r, f (x, r) -/
lemma _sum_pi_split
    {ι : Type} [Fintype ι] {X : ι → Type} [∀ i : ι, Fintype (X i)]
    (i : ι) (f : (∀ j : ι, X j) → ℝ) :
    ∑ s : (∀ j : ι, X j), f s
      = ∑ x : X i, ∑ r : (∀ j : {j // j ≠ i}, X j),
          f ((Equiv.piSplitAt i X).symm (x, r)) := by
  rw [← (Equiv.piSplitAt i X).symm.sum_comp, Fintype.sum_prod_type]

/-- `_pi_weight_split` (bookkeeping): the weight of `(x, r)` under `⨂ μ` is `μ_i(x) * μ_{-i}(r)`.

⊢ (⨂ μ)(x, r) = μ_i(x) * ∏_{j ≠ i} μ_j(r_j) -/
lemma _pi_weight_split
    {ι : Type} [Fintype ι] {X : ι → Type} [∀ i : ι, Fintype (X i)]
    (μ : ∀ i : ι, FinDist (X i)) (i : ι) (x : X i) (r : ∀ j : {j // j ≠ i}, X j) :
    (⨂ μ).w ((Equiv.piSplitAt i X).symm (x, r))
      = (μ i).w x * ∏ j : {j // j ≠ i}, (μ j).w (r j) := by
  simp only [FinDist.pi]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  congr 1
  · simp
  · exact Finset.prod_congr rfl (fun j _ => by simp [j.2])

/-- `_pi_update_weight_split` (bookkeeping): the weight of `(x, r)` under `⨂ (ν, μ_{-i})` is `ν(x) * μ_{-i}(r)`.

⊢ (⨂ (Function.update μ i ν))(x, r) = ν(x) * ∏_{j ≠ i} μ_j(r_j) -/
lemma _pi_update_weight_split
    {ι : Type} [Fintype ι] {X : ι → Type} [∀ i : ι, Fintype (X i)]
    (μ : ∀ i : ι, FinDist (X i)) (i : ι) (ν : FinDist (X i))
    (x : X i) (r : ∀ j : {j // j ≠ i}, X j) :
    (⨂ (Function.update μ i ν)).w ((Equiv.piSplitAt i X).symm (x, r))
      = ν.w x * ∏ j : {j // j ≠ i}, (μ j).w (r j) := by
  rw [_pi_weight_split]
  congr 1
  · simp
  · exact Finset.prod_congr rfl (fun j _ => by rw [Function.update_of_ne j.2])

/-- `_update_split` (bookkeeping): putting `x` in slot `i` of `(y, r)` gives `(x, r)`.

⊢ Function.update (y, r) i x = (x, r) -/
lemma _update_split
    {ι : Type} [Fintype ι] {X : ι → Type} [∀ i : ι, Fintype (X i)]
    (i : ι) (x y : X i) (r : ∀ j : {j // j ≠ i}, X j) :
    Function.update ((Equiv.piSplitAt i X).symm (y, r)) i x
      = (Equiv.piSplitAt i X).symm (x, r) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- `_sum_out` (algebra): summing out a variable drawn from a distribution `μ`.

⊢ ∑ a, ∑ b, μ(a) * g(b) = ∑ b, g(b) -/
lemma _sum_out (μ : FinDist α) (g : β → ℝ) :
    ∑ a : α, ∑ b : β, μ.w a * g b = ∑ b : β, g b := by
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_mul, μ.sum_one, one_mul]

/-- lemma `pi_update_bind`:
- μ : ∀ j, FinDist (X j) -- A mixed strategy profile
- i : ι -- fix agent i
- ν : FinDist (X i) -- a mixed strategy (deviation) of player i
- F : (∀ j, X j) → FinDist γ -- takes a pure action profile and return a random outcome

⊢ (⨂ (Function.update μ i ν)) >>= F = ν >>= (fun x ↦ (⨂ μ) >>= (fun s ↦ F (Function.update s i x)))

Left side: everyone draws independently from $(\nu, \mu_{-i})$, then you apply $F$ to the result.

Right side:

Draw $x \sim \nu$.
Draw a full profile $s \sim \bigotimes_j \mu_j$, including a draw $s_i \sim \mu_i$ for player $i$.
Throw away $s_i$, put $x$ in its place, and apply $F(x, s_{-i})$.
-/
lemma pi_update_bind
    {ι : Type} [Fintype ι] {X : ι → Type} [∀ i : ι, Fintype (X i)]
    (μ : ∀ i : ι, FinDist (X i))
    (i : ι)
    (ν : FinDist (X i))
    (F : (∀ j : ι, X j) → FinDist γ) :
    (⨂ (Function.update μ i ν)) >>= F
      = ν >>= (fun (x : X i) =>
          (⨂ μ) >>= (fun (s : ∀ j : ι, X j) =>
            F (Function.update s i x))) := by
  -- Fix an outcome `c`; write `G s := F(s)(c)`.
  ext c
  simp only [FinDist.bind]
  -- Split every `s` into `(s_i, s_{-i})`.
  -- L: the weight of `s` splits to `ν(s_i) μ_{-i}(s_{-i})`.
  simp only [_sum_pi_split i, _pi_update_weight_split]
  -- R: the weight of `s` splits to `μ_i(s_i) μ_{-i}(s_{-i})`, and `update (s_i, s_{-i}) i x = (x, s_{-i})`.
  simp only [_pi_weight_split, _update_split]
  -- R: sum out `s_i`.
  simp only [mul_assoc, _sum_out]
  -- R: move `ν(x)` inside; now L = R.
  simp only [Finset.mul_sum]

end FinDist

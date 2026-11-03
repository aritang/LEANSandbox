import CommHyp.Game

/-!
# The Revelation Principle (Myerson 1982, Forges 1986)

Proves that `μ` is a communication-equilibrium outcome if and only if `μ` is the
outcome of a truthful equilibrium under some direct device.

The key is to construct 'canonical' device `d* = canonical d π`.

Proof idea: any strategy `x` of player `i` in `G(d*)` can be mimicked in `G(d)`.
Player `i` feeds the type `x.report t` into a strategy `y` of `π i`, so the real
device `d` produces the action `a` that `d*` would recommend; then `i` plays
`x.act t (x.report t) a`. Same outcome ⇒ same payoff ⇒ `x` is not profitable.

* `canonical` — the canonical direct device `d*`, the witness
* `deviate`, `deviateMixed` — the mimicking strategy in `G(d)`
* `canonical_truthful_outcome_equivalence` — truthful play in `G(d*)` reproduces `outcome d π`
* `canonical_deviation_outcome_equivalence` — every deviation in `G(d*)` has a mimic with the same outcome
* `revelation_principle_canonical` — the main theorem, with `d*` explicit
* `revelation_principle` — the main theorem, as an existence statement
* `revelation_principle_iff` — the full statement, both directions

**Convention:** explicit code first, then a `Short form:` comment (see `Game.lean`).
-/

open Classical
noncomputable section

variable {ι : Type} [Fintype ι]
variable {T A M R : ι → Type}
variable [∀ i : ι, Fintype (T i)] [∀ i : ι, Fintype (A i)]
  [∀ i : ι, Fintype (M i)] [∀ i : ι, Fintype (R i)]

/-- `canonical` is a function that takes `d` and `π` and returns the direct device `d* : DirectDevice T A`: players report types and receive recommended actions drawn from `outcome d π`. -/
def canonical (d : Device M R) (π : MixStrategyProfile T A M R) : DirectDevice T A :=
  Device.mk (outcome d π)

/-- `deviate` is a function that takes a pure strategy `x` of player `i` in `G(d*)`
and a pure strategy `y` of player `i` in `G(d)` and returns the pure strategy in
`G(d)` that, at true type `t`, plays `y` as if the type were `x.report t`, then
applies `x.act` to `y`'s action. `x` may be any strategy, including `truthful i`
(then the result is `y`).

Flow (`t` = true type, `t̃ := x.report t` = the type `x` would report to `d*`):

```
x  (direct, in G(d*)):    report : T ──→ T̃
                           act    : T, T̃, A ──→ A

y  (general, in G(d)):    report : T ──→ M
                           act    : T, M, R ──→ A

y' = deviate x y  (in G(d)):
  report :  t ──x.report──→ t̃ ──y.report──→ m
  act    :  t, m, r ──→ x.act ( t , t̃ , y.act ( t̃ , m , r ) )
                               true  reported  └─ action d* would recommend
```
-/
def deviate {i : ι} (x : PureStrat T A T A i) (y : PureStrat T A M R i) :
    PureStrat T A M R i :=
  PureStrat.mk
    (fun (t : T i) => y.report (x.report t))
    (fun (t : T i) (m : M i) (r : R i) =>
      x.act t (x.report t) (y.act (x.report t) m r))

/-- `deviateMixed` is a function that takes a mixed strategy `ρ` of player `i` in
`G(d*)` and a mixed strategy `σ` of player `i` in `G(d)` and returns the mixed
strategy in `G(d)` that draws `(y, x) ∼ σ ⊗ ρ` and plays `y' ← deviate x y` -/
def deviateMixed {i : ι} (ρ : FinDist (PureStrat T A T A i))
    (σ : FinDist (PureStrat T A M R i)) : FinDist (PureStrat T A M R i) :=
  (σ.prod ρ).map (fun p => deviate p.2 p.1)

/-!
## Main result

**Revelation Principle** (`revelation_principle_iff`). For a Bayesian game `G` and an
outcome `μ : (∀ j, T j) → FinDist (∀ j, A j)`:

    μ is a communication-equilibrium outcome
      ⟺ μ is the outcome of a truthful equilibrium under some direct device.

`⇐` is immediate: a direct device is a device. `⇒` is proved in steps below:

0. `canonical` — construct the canonical device `d* = canonical d π` from `d` and `π`,
   which recommends actions drawn from `outcome d π`
1. `canonical_truthful_outcome_equivalence` — truthful play under `d*` reproduces `outcome d π` (Exercise 11)
2. `canonical_deviation_outcome_equivalence` — every deviation under `d*` has a mimic in `G(d)` (Exercise 12)
3. `revelation_principle_canonical` — so truthful play is an equilibrium under `d*`
4. `revelation_principle` — hence some direct device works
5. `revelation_principle_iff` — both directions together
-/

/-- lemma says `canonical_truthful_outcome_equivalence`: truthful play in `G(d*)` has the same outcome as `π` in `G(d)`. (Exercise 11) -/
lemma canonical_truthful_outcome_equivalence (d : Device M R) (π : MixStrategyProfile T A M R) (t : ∀ j : ι, T j) :
    outcome (canonical d π) truthfulProfile t = outcome d π t := sorry

/-- lemma `canonical_deviation_outcome_equivalence`: deviating to `ρ` in `G(d*)` has the same
outcome as deviating to `deviateMixed ρ (π i)` in `G(d)`. (Exercise 12, the key step) -/
lemma canonical_deviation_outcome_equivalence (d : Device M R) (π : MixStrategyProfile T A M R) (i : ι)
    (ρ : FinDist (PureStrat T A T A i)) (t : ∀ j : ι, T j) :
    outcome (canonical d π) (Function.update truthfulProfile i ρ) t =
      outcome d (Function.update π i (deviateMixed ρ (π i))) t := sorry

/-- theorem `revelation_principle_canonical`: if `π` is a communication
equilibrium of `G(d)`, then truthful play is a communication equilibrium of `G(d*)`
with the same outcome. -/
theorem revelation_principle_canonical (G : BayesGame T A) (d : Device M R) (π : MixStrategyProfile T A M R)
    (h : IsCommunicationEq G d π) :
    IsCommunicationEq G (canonical d π) truthfulProfile ∧
      ∀ t : (∀ j : ι, T j), outcome (canonical d π) truthfulProfile t = outcome d π t := by
  refine And.intro (fun (i : ι) (ρ : FinDist (PureStrat T A T A i)) => ?_)
    (canonical_truthful_outcome_equivalence d π)
  -- the deviation's payoff equals the mimicking deviation's payoff in G(d)
  have hdev : payoff G (canonical d π) (Function.update truthfulProfile i ρ) i =
      payoff G d (Function.update π i (deviateMixed ρ (π i))) i := by
    simp only [payoff, canonical_deviation_outcome_equivalence]
  -- truthful play's payoff equals the equilibrium payoff in G(d)
  have htr : payoff G (canonical d π) truthfulProfile i = payoff G d π i := by
    simp only [payoff, canonical_truthful_outcome_equivalence]
  rw [hdev, htr]
  exact h i (deviateMixed ρ (π i))
/- Short form of the proof:
  refine ⟨fun i ρ => ?_, canonical_truthful_outcome_equivalence d π⟩
  ...
  exact h i _ -/

/-- theorem `revelation_principle`: if `π` is a communication equilibrium of
`G(d)`, then there exists a direct device `d'` under which truthful play is a
communication equilibrium with the same outcome as `π` in `G(d)`. -/
theorem revelation_principle (G : BayesGame T A) (d : Device M R)
    (π : MixStrategyProfile T A M R) (h : IsCommunicationEq G d π) :
    ∃ (d' : DirectDevice T A),
      IsCommunicationEq G d' truthfulProfile ∧
      ∀ (t : ∀ j : ι, T j), outcome d' truthfulProfile t = outcome d π t :=
  Exists.intro (canonical d π) (revelation_principle_canonical G d π h)
/- Short form:
  ⟨canonical d π, revelation_principle_canonical G d π h⟩ -/

/-- theorem `revelation_principle_iff`: `μ` is a communication-equilibrium outcome
of `G` if and only if some direct device `d'` has truthful play as a communication
equilibrium with outcome `μ`. -/
theorem revelation_principle_iff (G : BayesGame T A)
    (μ : (∀ j : ι, T j) → FinDist (∀ j : ι, A j)) :
    IsCommunicationEqOutcome G μ ↔
      ∃ (d' : DirectDevice T A),
        IsCommunicationEq G d' truthfulProfile ∧
        ∀ (t : ∀ j : ι, T j), outcome d' truthfulProfile t = μ t := by
  apply Iff.intro
  · -- ⇒: unpack the device and equilibrium, then apply `revelation_principle`
    intro hOut
    obtain ⟨M', R', hM', hR', d, π, h, hμ⟩ := hOut
    obtain ⟨d', h1, h2⟩ := revelation_principle G d π h
    exact Exists.intro d'
      (And.intro h1 (fun (t : ∀ j : ι, T j) => Eq.trans (h2 t) (hμ t)))
  · -- ⇐: a direct device is a device; take `M := T`, `R := A`, `π := truthfulProfile`
    intro hDir
    obtain ⟨d', h1, h2⟩ := hDir
    exact ⟨T, A, inferInstance, inferInstance, d', truthfulProfile, h1, h2⟩

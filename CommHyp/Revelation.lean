import CommHyp.Game

/-!
# The Revelation Principle (Myerson 1982, Forges 1986)

`μ` is a communication-equilibrium outcome if and only if it is the outcome of truthful play in a communication equilibrium with some direct device.

`d*` means `canonical d π`.

**Convention:** explicit code first, then a `Short form:` comment (see `Game.lean`).
-/

open Classical
noncomputable section

variable {ι : Type} [Fintype ι]
variable {T A M R : ι → Type}
variable [∀ i : ι, Fintype (T i)] [∀ i : ι, Fintype (A i)] [∀ i : ι, Fintype (M i)] [∀ i : ι, Fintype (R i)]

/-!
## Main result

Proof of "only if", in steps:

0. `canonical`: the direct device `d*`.
1. `canonical_truthful_outcome_equivalence`: truthful play with `d*` gives `outcome d π` (Exercise 11).
2. `canonical_deviation_outcome_equivalence`: each deviation with `d*` has a copy with `d`, same outcome (Exercise 12).
3. `revelation_principle_canonical`: so truthful play is an equilibrium with `d*`.
4. `revelation_principle`: so some direct device works.
5. `revelation_principle_iff`: both directions.
-/

/-- `canonical d π` is the direct device that, given reported types `t`, recommends actions drawn from `outcome d π t`. -/
def canonical (d : Device M R) (π : MixStrategyProfile T A M R) : DirectDevice T A :=
  Device.mk (outcome d π)

/-- lemma `canonical_truthful_outcome_equivalence`: truthful play with `d*` has the same outcome as `π` with `d`. -/
lemma canonical_truthful_outcome_equivalence (d : Device M R) (π : MixStrategyProfile T A M R) (t : ∀ j : ι, T j) : outcome (canonical d π) truthfulProfile t = outcome d π t := by
  -- Step 1: unfold the definitions.
  unfold outcome truthfulProfile
  -- Step 2: everyone plays `truthful` for sure (`pi_pure`).
  rw [FinDist.pi_pure (fun (i : ι) => truthful i)]
  -- Step 3: so the outcome is `play d* truthful t` (`pure_bind`).
  rw [FinDist.pure_bind]
  -- Step 4: truthful players report `t` and play what `d*` recommends, so the goal is `map (fun a => a) (outcome d π t) = outcome d π t`.
  unfold play canonical truthful
  simp only
  -- Step 5: mapping by the identity changes nothing (`map_id'`).
  exact FinDist.map_id' (outcome d π t)
/- Short form:
  unfold outcome truthfulProfile
  rw [FinDist.pi_pure, FinDist.pure_bind]
  exact FinDist.map_id' _ -/


/-- `deviate x y`

x is pure direct strategy of i (PureStrat T A T A i)
y is general pure strategy of i (PureStrat T A M R i)
y' <- deviate x y is (returns) general pure strategy of i (PureStrat T A M R i): play `y` as if the type were `x.report t`, then apply `x.act` to the resulting action.

```
report :  t  ──x.report──→  t'  ──y.report──→  m
act    :  t, m, r  ──→  x.act t t' (y.act t' m r)
```
-/
def deviate {i : ι} (x : PureStrat T A T A i) (y : PureStrat T A M R i) : PureStrat T A M R i :=
  PureStrat.mk
    (fun (t : T i) => y.report (x.report t))
    (fun (t : T i) (m : M i) (r : R i) =>
      x.act t (x.report t) (y.act (x.report t) m r))


/-- `deviateMixed ρ σ`
ρ is Mixed Direct Strategy of i (PureStrat T A T A i)
σ is Mixed Strategy of i (PureStrat T A M R i)
returns the distribution of y' ~ deviate x y, with x ~ ρ, y ~ σ
-/
def deviateMixed {i : ι} (ρ : FinDist (PureStrat T A T A i)) (σ : FinDist (PureStrat T A M R i)) : FinDist (PureStrat T A M R i) :=
  (σ.prod ρ).map (fun p => deviate p.2 p.1)

/-- lemma `canonical_deviation_outcome_equivalence`:
Fix
d : Device M R
π : MixStrategyProfile T A M R
i : ι -- the deviating agent
ρ : FinDist (PureStrat T A T A i) -- i's mixed direct strategy to deviate to
t : (j : ι) → T j -- everyone's type profile
then: outcome (canonical d π) (Function.update truthfulProfile i ρ) t =
  outcome d (Function.update π i (deviateMixed ρ (π i))) t
-/
lemma canonical_deviation_outcome_equivalence (d : Device M R) (π : MixStrategyProfile T A M R) (i : ι) (ρ : FinDist (PureStrat T A T A i)) (t : ∀ j : ι, T j) : outcome (canonical d π) (Function.update truthfulProfile i ρ) t = outcome d (Function.update π i (deviateMixed ρ (π i))) t := by
  simp [canonical, ]
  sorry


/-- theorem `revelation_principle_canonical`: if `π` is a communication equilibrium with `d`, truthful play is one with `d*`, with the same outcome. -/
theorem revelation_principle_canonical (G : BayesGame T A) (d : Device M R) (π : MixStrategyProfile T A M R) (h : IsCommunicationEq G d π) : IsCommunicationEq G (canonical d π) truthfulProfile ∧ ∀ t : (∀ j : ι, T j), outcome (canonical d π) truthfulProfile t = outcome d π t := by
  refine And.intro (fun (i : ι) (ρ : FinDist (PureStrat T A T A i)) => ?_) (canonical_truthful_outcome_equivalence d π)
  -- deviating to `ρ` with `d*` pays the same as deviating to `deviateMixed ρ (π i)` with `d`
  have hdev : payoff G (canonical d π) (Function.update truthfulProfile i ρ) i = payoff G d (Function.update π i (deviateMixed ρ (π i))) i := by
    simp only [payoff, canonical_deviation_outcome_equivalence]
  -- truthful play with `d*` pays the same as `π` with `d`
  have htr : payoff G (canonical d π) truthfulProfile i = payoff G d π i := by
    simp only [payoff, canonical_truthful_outcome_equivalence]
  rw [hdev, htr]
  exact h i (deviateMixed ρ (π i))
/- Short form of the proof:
  refine ⟨fun i ρ => ?_, canonical_truthful_outcome_equivalence d π⟩
  ...
  exact h i _ -/

/-- theorem `revelation_principle`: if `π` is a communication equilibrium with `d`, some direct device has truthful play as an equilibrium with the same outcome. -/
theorem revelation_principle (G : BayesGame T A) (d : Device M R) (π : MixStrategyProfile T A M R) (h : IsCommunicationEq G d π) : ∃ (d' : DirectDevice T A), IsCommunicationEq G d' truthfulProfile ∧ ∀ (t : ∀ j : ι, T j), outcome d' truthfulProfile t = outcome d π t :=
  Exists.intro (canonical d π) (revelation_principle_canonical G d π h)
/- Short form:
  ⟨canonical d π, revelation_principle_canonical G d π h⟩ -/

/-- theorem `revelation_principle_iff`: `μ` is a communication-equilibrium outcome iff it is the outcome of a truthful equilibrium with some direct device. -/
theorem revelation_principle_iff (G : BayesGame T A) (μ : (∀ j : ι, T j) → FinDist (∀ j : ι, A j)) : IsCommunicationEqOutcome G μ ↔ ∃ (d' : DirectDevice T A), IsCommunicationEq G d' truthfulProfile ∧ ∀ (t : ∀ j : ι, T j), outcome d' truthfulProfile t = μ t := by
  apply Iff.intro
  · -- "only if": unpack the device and equilibrium, then apply `revelation_principle`
    intro hOut
    obtain ⟨M', R', hM', hR', d, π, h, hμ⟩ := hOut
    obtain ⟨d', h1, h2⟩ := revelation_principle G d π h
    exact Exists.intro d' (And.intro h1 (fun (t : ∀ j : ι, T j) => Eq.trans (h2 t) (hμ t)))
  · -- "if": a direct device is a device; take `M := T`, `R := A`, `π := truthfulProfile`
    intro hDir
    obtain ⟨d', h1, h2⟩ := hDir
    exact ⟨T, A, inferInstance, inferInstance, d', truthfulProfile, h1, h2⟩

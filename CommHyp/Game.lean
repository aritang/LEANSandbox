import CommHyp.FinDist

/-!
# Bayesian games and communication equilibrium

Players `i : ι` with types `T i`, actions `A i`, messages `M i`, signals `R i` (all finite). `G(d)` means the game `G` played with device `d`.

**Convention:** explicit code first, then a `Short form:` comment. Explicit means binder types written out, functions called by full name (`FinDist.map f μ`, not `μ.map f`), and anonymous constructors written out (`Device.mk x`, not `⟨x⟩`). Structure fields use dot notation in both forms (`d.q`, `G.p`, `(s i).report`).
-/
open Classical
noncomputable section

variable {ι : Type} [Fintype ι]
variable {T A M R : ι → Type}
variable [hT : ∀ i : ι, Fintype (T i)] [hA : ∀ i : ι, Fintype (A i)] [hM : ∀ i : ι, Fintype (M i)] [hR : ∀ i : ι, Fintype (R i)]


/-- `BayesGame T A` is a Bayesian game: a prior `p` on type profiles and payoffs `u i a t`. -/
structure BayesGame (T A : ι → Type) [∀ i : ι, Fintype (T i)] where
  p : FinDist (∀ i : ι, T i)
  u : ι → (∀ i : ι, A i) → (∀ i : ι, T i) → ℝ

/-- `Device M R` is a device: `q m` is the distribution of signal profiles given message profile `m`. -/
structure Device (M R : ι → Type) [∀ i : ι, Fintype (R i)] where
  q : (∀ i : ι, M i) → FinDist (∀ i : ι, R i)

/-- `ReportRule T M i` is a map from player `i`'s type to `i`'s message. -/
abbrev ReportRule (T M : ι → Type) (i : ι) : Type :=
  T i → M i

/-- `ActionRule T A M R i` is a map from player `i`'s type, message and signal to `i`'s action. -/
abbrev ActionRule (T A M R : ι → Type) (i : ι) : Type :=
  T i → M i → R i → A i

/-- `PureStrat T A M R i` is a pure strategy of player `i`: a report rule and an action rule. -/
structure PureStrat (T A M R : ι → Type) (i : ι) : Type where
  report : ReportRule T M i
  act : ActionRule T A M R i

/-- `PureStrat._equivProd i`: a pure strategy is a pair (report rule, action rule). -/
private def PureStrat._equivProd
    (i : ι) :
    PureStrat T A M R i ≃ ReportRule T M i × ActionRule T A M R i where
  toFun := fun (s : PureStrat T A M R i) => (s.report, s.act)
  invFun := fun (p : ReportRule T M i × ActionRule T A M R i) => PureStrat.mk p.1 p.2
  left_inv := fun (_ : PureStrat T A M R i) => rfl
  right_inv := fun (_ : ReportRule T M i × ActionRule T A M R i) => rfl

/-- `PureStrat T A M R i` is finite, so `FinDist (PureStrat T A M R i)` makes sense. -/
instance (i : ι) : Fintype (PureStrat T A M R i) :=
  Fintype.ofEquiv (ReportRule T M i × ActionRule T A M R i) (PureStrat._equivProd i).symm

/-- `MixStrategyProfile T A M R` is a mixed strategy profile: `π i` is player `i`'s distribution over pure strategies. -/
abbrev MixStrategyProfile
    (T A M R : ι → Type)
    [∀ i : ι, Fintype (T i)] [∀ i : ι, Fintype (A i)] [∀ i : ι, Fintype (M i)]
    [∀ i : ι, Fintype (R i)] :
    Type :=
  ∀ i : ι, FinDist (PureStrat T A M R i)

/-- `play d s t` returns the distribution of action profiles when types are `t` and players play pure strategies `s` with device `d`. -/
def play
    (d : Device M R)
    (s : ∀ i : ι, PureStrat T A M R i)
    (t : ∀ i : ι, T i) :
    FinDist (∀ i : ι, A i) :=
  -- Step 1: each player `i` reports a message based on their own type.
  let m : ∀ i : ι, M i := fun (i : ι) => (s i).report (t i)
  -- Step 2: the device maps the message profile to a distribution of signal profiles.
  let signals : FinDist (∀ i : ι, R i) := d.q m
  -- Step 3: given a signal profile `r`, each player `i` acts on their own type, message and signal.
  let respond : (∀ i : ι, R i) → (∀ i : ι, A i) :=
    fun (r : ∀ i : ι, R i) (i : ι) => (s i).act (t i) (m i) (r i)
  -- Result: pick `r` from `signals`, output the action profile `respond r`.
  FinDist.map respond signals

/-- `outcome d π t` returns the distribution of action profiles when types are `t` and players play mixed strategies `π` with device `d`. -/
def outcome
    (d : Device M R)
    (π : MixStrategyProfile T A M R)
    (t : ∀ i : ι, T i) :
    FinDist (∀ i : ι, A i) :=
  FinDist.bind (FinDist.pi π) (fun (s : ∀ i : ι, PureStrat T A M R i) => play d s t)

/-- `payoff G d π i` returns player `i`'s expected payoff (over types and actions). -/
def payoff (G : BayesGame T A) (d : Device M R) (π : MixStrategyProfile T A M R) (i : ι) : ℝ :=
  FinDist.E G.p
    (fun (t : ∀ j : ι, T j) =>
      FinDist.E (outcome d π t)
        (fun (a : ∀ j : ι, A j) =>
          G.u i a t))


/-- `IsCommunicationEq G d π` says no player `i` gains by switching to another mixed strategy `ρ`. -/
def IsCommunicationEq
    (G : BayesGame T A)
    (d : Device M R)
    (π : MixStrategyProfile T A M R) :
    Prop :=
  ∀ (i : ι) (ρ : FinDist (PureStrat T A M R i)),
    payoff G d (Function.update π i ρ) i ≤ payoff G d π i

/-- `IsCommunicationEqOutcome G μ` says `μ` is the outcome of some communication equilibrium with some device. -/
def IsCommunicationEqOutcome
    (G : BayesGame T A)
    (μ : (∀ j : ι, T j) → FinDist (∀ j : ι, A j)) :
    Prop :=
  ∃ (M R : ι → Type) (_ : ∀ i : ι, Fintype (M i)) (_ : ∀ i : ι, Fintype (R i))
    (d : Device M R) (π : MixStrategyProfile T A M R),
    IsCommunicationEq G d π ∧ ∀ (t : ∀ j : ι, T j), outcome d π t = μ t

/-- `DirectDevice T A` is a device whose messages are types and whose signals are actions. -/
abbrev DirectDevice (T A : ι → Type) [∀ i : ι, Fintype (A i)] : Type :=
  Device T A

/-- `truthful i` reports the true type and plays the recommended action. -/
def truthful (i : ι) : PureStrat T A T A i :=
PureStrat.mk
  (fun (t : T i) => t)                          -- report rule
  (fun (_t : T i) (_m : T i) (a : A i) => a)    -- action rule

/-- `truthfulProfile` has every player `i` play `truthful i` for sure. -/
def truthfulProfile : MixStrategyProfile T A T A :=
  fun (i : ι) => FinDist.pure (truthful i)

import CommHyp.FinDist

/-!
# Bayesian games and communication equilibrium

Defines a finite Bayesian game `G`, a communication device `d`, play in the
extended game `G(d)`, and communication equilibrium — the setting for the
Revelation Principle in `Revelation.lean`.

Players `ι`; types `T i`, actions `A i`, messages `M i`, signals `R i`, all finite.

* `BayesGame T A` — prior `p` on type profiles and payoffs `u`
* `Device M R` — maps a message profile to a distribution of signal profiles
* `outcome d π` — the distribution of action profiles `T → Δ(A)` under `π` in `G(d)`
* `IsCommunicationEq G d π` — no player gains by deviating unilaterally
* `IsCommunicationEqOutcome G μ` — `μ` is produced by some device and equilibrium
* `DirectDevice T A`, `truthfulProfile` — devices with `M = T`, `R = A`, and honest-obedient play

**Convention:** explicit code first, then a `Short form:` comment. Explicit means
binder types written out, functions called by full name (`FinDist.map f μ`, not
`μ.map f`), and anonymous constructors written out (`Device.mk x`, not `⟨x⟩`).
Structure fields use dot notation in both forms (`d.q`, `G.p`, `(s i).report`).
-/
open Classical
noncomputable section

variable {ι : Type} [Fintype ι]
variable {T A M R : ι → Type}
variable [hT : ∀ i : ι, Fintype (T i)] [hA : ∀ i : ι, Fintype (A i)] [hM : ∀ i : ι, Fintype (M i)] [hR : ∀ i : ι, Fintype (R i)]


/-- `BayesGame` is a structure that takes type spaces `T` and action spaces `A`
and bundles a common prior `p : FinDist (∀ i, T i)` with payoffs
`u i : (action profile) → (type profile) → ℝ`. -/
structure BayesGame (T A : ι → Type) [∀ i : ι, Fintype (T i)] where
  p : FinDist (∀ i : ι, T i)
  u : ι → (∀ i : ι, A i) → (∀ i : ι, T i) → ℝ

/-- `Device` is a structure that takes message spaces `M` and signal spaces `R` and
bundles a map `q` from message profiles to distributions of signal profiles. -/
structure Device (M R : ι → Type) [∀ i : ι, Fintype (R i)] where
  q : (∀ i : ι, M i) → FinDist (∀ i : ι, R i)

/-- `ReportRule` is a type: player `i`'s map from own type to the message sent. -/
abbrev ReportRule (T M : ι → Type) (i : ι) : Type :=
  T i → M i

/-- `ActionRule` is a type: player `i`'s map from own type, sent message and
received signal to the action taken. -/
abbrev ActionRule (T A M R : ι → Type) (i : ι) : Type :=
  T i → M i → R i → A i

/-- `PureStrat` is a structure: a pure strategy of player `i` in `G(d)`, bundling
a report rule `report` and an action rule `act`. -/
structure PureStrat (T A M R : ι → Type) (i : ι) : Type where
  report : ReportRule T M i
  act : ActionRule T A M R i

/-- `PureStrat._equivProd` is an equivalence between `PureStrat T A M R i` and the
pair type `ReportRule T M i × ActionRule T A M R i`. -/
private def PureStrat._equivProd (i : ι) :
    PureStrat T A M R i ≃ ReportRule T M i × ActionRule T A M R i where
  toFun := fun (s : PureStrat T A M R i) => (s.report, s.act)
  invFun := fun (p : ReportRule T M i × ActionRule T A M R i) => PureStrat.mk p.1 p.2
  left_inv := fun (_ : PureStrat T A M R i) => rfl
  right_inv := fun (_ : ReportRule T M i × ActionRule T A M R i) => rfl

/-- `PureStrat` is finite, via `PureStrat._equivProd` (needed for `FinDist (PureStrat …)`). -/
instance (i : ι) : Fintype (PureStrat T A M R i) :=
  Fintype.ofEquiv (ReportRule T M i × ActionRule T A M R i) (PureStrat._equivProd i).symm

/-- `MixStrategyProfile` is a type: a mixed strategy profile, one distribution over pure
strategies per player (players randomize independently). -/
abbrev MixStrategyProfile (T A M R : ι → Type)
    [∀ i : ι, Fintype (T i)] [∀ i : ι, Fintype (A i)]
    [∀ i : ι, Fintype (M i)] [∀ i : ι, Fintype (R i)] : Type :=
  ∀ i : ι, FinDist (PureStrat T A M R i)

/-- `play` is a function that takes a device `d`, pure strategies `s` and a type
profile `t` and returns the distribution of action profiles: each `i` reports
`(s i).report (t i)`, the device draws signals `r`, and `i` plays `(s i).act`. -/
def play (d : Device M R) (s : ∀ i : ι, PureStrat T A M R i) (t : ∀ i : ι, T i) :
    FinDist (∀ i : ι, A i) :=
  -- Step 1: each player `i` reports a message based on their own type.
  let m : ∀ i : ι, M i := fun (i : ι) => (s i).report (t i)
  -- Step 2: the device maps the message profile to a distribution of signal profiles.
  let signals : FinDist (∀ i : ι, R i) := d.q m
  -- Step 3: given a drawn signal profile `r`, each player `i` acts on
  -- their own type, message and signal.
  let respond : (∀ i : ι, R i) → (∀ i : ι, A i) :=
    fun (r : ∀ i : ι, R i) (i : ι) => (s i).act (t i) (m i) (r i)
  -- Result: push the signal distribution forward through `respond`.
  FinDist.map respond signals

/-- `outcome` is a function that takes a device `d`, a mixed profile `π` and a type
profile `t` and returns the distribution of action profiles, `μ(· ∣ t)`. -/
def outcome (d : Device M R) (π : MixStrategyProfile T A M R) (t : ∀ i : ι, T i) :
    FinDist (∀ i : ι, A i) :=
  FinDist.bind (FinDist.pi π) (fun (s : ∀ i : ι, PureStrat T A M R i) => play d s t)

/-- `payoff` is a function that takes `G`, `d`, `π` and a player `i` and returns
`i`'s ex-ante expected payoff `E_t E_{a ∼ μ(·∣t)} [u i a t] : ℝ`. -/
def payoff (G : BayesGame T A) (d : Device M R) (π : MixStrategyProfile T A M R) (i : ι) : ℝ :=
  FinDist.E G.p
    (fun (t : ∀ j : ι, T j) =>
      FinDist.E (outcome d π t)
        (fun (a : ∀ j : ι, A j) =>
          G.u i a t))


/-- `IsCommunicationEq` is a predicate on `G`, `d`, `π`: `π` is a communication equilibrium,
i.e. no player `i` gains by switching to any other mixed strategy `ρ`. -/
def IsCommunicationEq (G : BayesGame T A) (d : Device M R) (π : MixStrategyProfile T A M R) : Prop :=
  ∀ (i : ι) (ρ : FinDist (PureStrat T A M R i)),
    payoff G d (Function.update π i ρ) i ≤ payoff G d π i

/-- `IsCommunicationEqOutcome` is a predicate on `G` and `μ : T → Δ(A)`: there exist
message and signal spaces `M R`, a device `d` and a communication equilibrium `π` of
`G(d)` whose outcome is `μ`. -/
def IsCommunicationEqOutcome (G : BayesGame T A)
    (μ : (∀ j : ι, T j) → FinDist (∀ j : ι, A j)) : Prop :=
  ∃ (M R : ι → Type) (_ : ∀ i : ι, Fintype (M i)) (_ : ∀ i : ι, Fintype (R i))
    (d : Device M R) (π : MixStrategyProfile T A M R),
    IsCommunicationEq G d π ∧ ∀ (t : ∀ j : ι, T j), outcome d π t = μ t

/-- `DirectDevice` is a type: a device whose messages are types and whose signals
are recommended actions (`M = T`, `R = A`). -/
abbrev DirectDevice (T A : ι → Type) [∀ i : ι, Fintype (A i)] : Type :=
  Device T A

/-- `truthful` is player `i`'s pure strategy under a direct device that reports
the true type and plays the recommended action. -/
def truthful (i : ι) : PureStrat T A T A i :=
PureStrat.mk
  (fun (t : T i) => t)                          -- report rule
  (fun (_t : T i) (_m : T i) (a : A i) => a)    -- action rule

/-- `truthfulProfile` is the profile in which every player plays `truthful` for sure. -/
def truthfulProfile : MixStrategyProfile T A T A :=
  fun (i : ι) => FinDist.pure (truthful i)

/-!
# Praxeology in Lean 4

A formalization of the Hilbert-style axiomatization of praxeology
following Komendarczyk, Block, Levendis, and Tipler,
"An Axiomatization of Praxeology --- Foundations" (2026).

This file is **self-contained**: it imports nothing and uses only
Lean 4 core (no Mathlib). If everything compiles cleanly, every
theorem and every axiom of the Crusoe model is verified.

## How to run this file

  1. **Web playground (easiest, no install needed):**
     Go to https://live.lean-lang.org
     Paste this entire file. Wait ~30 seconds for compilation.
     Errors (if any) appear underlined and in the right-hand panel.

  2. **Local install with VS Code:**
     Install Lean 4 from https://docs.lean-lang.org/lean4/doc/quickstart.html
     Install the "lean4" extension in VS Code, save this file as
     `Praxeology.lean`, and open it. The Lean Infoview shows the
     proof state as you click around.

  3. **Command line:**
     With Lean installed: `lean Praxeology.lean`
     (No output = all proofs succeeded.)

## What this file verifies

The Crusoe instance is the **nets-and-boats** Crusoe of the
Foundations paper §3.6, extended in anticipation of future
research with a production enrichment (Result/Consumable
predicates, higher-order-goods hierarchy). Five actions
(Forage, BuildNet, ShoreFish, BuildBoat, DeepSeaFish), four
ends (Subsist, Capital, ShoreCatch, DeepCatch — BuildNet and
BuildBoat share the Capital end), six things (Wood, Net, Boat,
Plant, Fish, Tuna), three time points (t0 < t1 < t2).
Availability menus grow monotonically as capital accumulates
({2 actions} ⊂ {4} ⊂ {5}); Crusoe's chosen history is
BuildNet@t0, BuildBoat@t1, DeepSeaFish@t2. Recipes (Use/Result):
BuildNet uses Wood, produces Net; ShoreFish uses Net, produces
Fish; BuildBoat uses Wood, produces Boat; DeepSeaFish uses
Net+Boat, produces Tuna; Forage produces Plant (no input).
Three things are consumable: Plant, Fish, Tuna.

Lean verifies (i) every base axiom T1–T4, P1–P5, C1 by exhaustive
case analysis; (ii) the standard derived theorems (asymmetry of
revealed preference, opportunity cost) on this model; (iii) every
CrusoeThing has a finite Order in the recursive higher-order-goods
hierarchy (Plant/Fish/Tuna at order 1, Net/Boat at order 2,
Wood at order 3). Acceptance of the `crusoeModel` instance is a
constructive consistency proof of T_prx (with the production
enrichment) on this model.

Sections 8–10 add the (MU)-enrichment of the Foundations paper
§3.2: the new sort `Good`, the predicates `UnitOf`, `Allot`, and
`Pref`, the order axioms (O2)/(O3) `Pref_comp`/`Pref_trans` with
asymmetry `Pref_asymm`, both halves of (MU0), and (MU4)
top-segment — in its corrected form, relativized to the good's
*serviceable* ends.  Then the diminishing-marginal-utility
theorem (`thm:DMU` of the Foundations paper §3.2) and its
structure-preservation corollary (`cor:dmu_structure`) are
stated and machine-verified, mirroring the appendix proof
`app:dmu_proof`.

Section 11 adds a worked (MU)-instance: the two-good water/fish
allotment schedule from the Crusoe box accompanying (MU4) in the
paper, in which two goods alternate down a single value scale.
Lean's acceptance of `waterFishModel` proves the relativized
(MU4) admits this multi-good case, and an `example` verifies
that the old *unrelativized* form of (MU4) fails on it — the
reason the axiom had to be corrected.

Further enrichments — ownership, exchange, monetary calculation,
and the transition map — are deferred to future Lean stages,
paralleling the future-research directions sketched in §5
of the Foundations paper.
-/

----------------------------------------------------------------
-- SECTION 1.  The Praxeological Class (base + E5)
----------------------------------------------------------------

/-- A `Praxeology` packages the sorts, primitive relations, and
    axioms of the formal language L_prx from the paper. An *instance*
    of this class is a *model* of the theory T_prx in the sense of
    Hilbert and Tarski: a structure satisfying all the axioms.

    The five sorts are: Actor, Action, EndE, Thing, Time.
    The base primitive relations are: Lt, Acts, Avail, EndOf, Use.
    The E5 production-enrichment relations are: Result, Consumable.

    Note: we name the sort of ends `EndE` because `End` is reserved
    by Lean. -/
class Praxeology where
  -- The five sorts (each is a Type)
  Actor   : Type
  Action  : Type
  EndE    : Type
  Thing   : Type
  Time    : Type

  -- Base primitive relations
  Lt      : Time → Time → Prop                   -- "t < s"
  Acts    : Actor → Action → Time → Prop          -- "a does α at t"
  Avail   : Actor → Action → Time → Prop          -- "α available to a at t"
  EndOf   : Action → EndE → Prop                  -- "α aims at end E"
  Use     : Action → Thing → Prop                 -- "α employs thing x"

  -- E5 production-enrichment relations
  Result     : Action → Thing → Prop              -- "α produces thing x"
  Consumable : Thing → Prop                       -- "x directly satisfies wants"

  -- TIME-ORDER AXIOMS  (T1–T4)
  T1_irrefl  : ∀ t : Time, ¬ Lt t t
  T2_trans   : ∀ t s r : Time, Lt t s → Lt s r → Lt t r
  T3_trichot : ∀ t s : Time, Lt t s ∨ t = s ∨ Lt s t
  T4_nontriv : ∃ t s : Time, Lt t s

  -- INCIDENCE AXIOMS  (P1–P5)
  P1 : ∀ (a : Actor) (t : Time), ∃ α : Action, Avail a α t
  P2 : ∀ (a : Actor) (α : Action) (t : Time), Acts a α t → Avail a α t
  P3 : ∀ α : Action, ∃ E : EndE, EndOf α E
  P4 : ∀ (α : Action) (E F : EndE), EndOf α E → EndOf α F → E = F
  P5 : ∀ (a : Actor) (α β : Action) (t s : Time),
       Acts a α t → Acts a β s → α ≠ β → t ≠ s

  -- CHOICE AXIOM  (C1)
  C1 : ∀ (a : Actor) (t : Time) (α β : Action),
       Acts a α t → Acts a β t → α = β

----------------------------------------------------------------
-- SECTION 2.  Revealed Preference  (definition, not axiom)
----------------------------------------------------------------

/-- The *revealed-preference relation* (`def:revpref` of the
    Foundations paper): `RevPref a t E F` says actor `a` puts end
    `E` over end `F` on record at time `t` — `a` chose an action
    whose end is `E` while an action whose end is the *different*
    end `F` was simultaneously available.  The leading `E ≠ F`
    clause excludes the degenerate self-revelation that means-ends
    multiplicity would otherwise generate (two available actions
    sharing one end).  Under the paper's redesign the record is
    *defined* from choice, while the preference order itself is a
    primitive grounded in the record by axiom (O0) — see
    `PraxeologyFull` below. -/
def Praxeology.RevPref [P : Praxeology]
    (a : P.Actor) (t : P.Time) (E F : P.EndE) : Prop :=
  E ≠ F ∧ ∃ α β : P.Action,
    P.Acts a α t ∧ P.Avail a β t ∧ α ≠ β ∧
    P.EndOf α E ∧ P.EndOf β F

----------------------------------------------------------------
-- SECTION 3.  The higher-order-goods hierarchy (E5 derived)
----------------------------------------------------------------

/-- The recursive `Order(x, n)` predicate of the production-enrichment (future research)
    A consumable good has order 1; a good `x` used by some action
    whose result is at order `n` is itself at order `n+1`.
    The two PH-axioms (PH1 value-dependency, PH2 grounding-in-
    consumption) follow respectively from the constructors of this
    inductive type and from the per-instance theorem
    `*_Order_total` proved below. -/
inductive Praxeology.Order [P : Praxeology] : P.Thing → Nat → Prop
  | base
      (x : P.Thing) (h : P.Consumable x)
      : Praxeology.Order x 1
  | step
      (x : P.Thing) (α : P.Action) (y : P.Thing) (n : Nat)
      (hres : P.Result α y) (huse : P.Use α x)
      (hy   : Praxeology.Order y n)
      : Praxeology.Order x (n + 1)

----------------------------------------------------------------
-- SECTION 4.  Theorems
----------------------------------------------------------------

namespace Praxeology
variable [P : Praxeology]

/-- **Lemma.**  If actor `a` reveals **both** `E ≻ F` and `F ≻ E`
    at the same time `t`, then `E = F`.

    *Proof.* Each preference revelation gives us a chosen action.
    By the choice axiom C1, the two chosen actions must be equal.
    By the unique-end axiom P4, that single action's end is both
    `E` and `F`, hence `E = F`. -/
theorem revPref_eq_of_both
    (a : P.Actor) (t : P.Time) (E F : P.EndE)
    (h₁ : RevPref a t E F) (h₂ : RevPref a t F E) : E = F := by
  obtain ⟨_, α₁, _, hα₁_acts, _, _, hα₁_E, _⟩ := h₁
  obtain ⟨_, α₂, _, hα₂_acts, _, _, hα₂_F, _⟩ := h₂
  have heq : α₁ = α₂ := P.C1 a t α₁ α₂ hα₁_acts hα₂_acts
  rw [heq] at hα₁_E
  exact P.P4 α₂ E F hα₁_E hα₂_F

/-- **Asymmetry of revealed preference (`thm:asymm`).**  Valid
    without restriction: the `E ≠ F` clause of the definition
    makes the reflexive instance vacuous, so — unlike the
    pre-redesign form — no distinctness hypothesis is needed.
    A single moment of conduct cannot put contradictory pairs on
    record. -/
theorem revPref_asymm
    (a : P.Actor) (t : P.Time) (E F : P.EndE)
    (h : RevPref a t E F) : ¬ RevPref a t F E := by
  intro h'
  exact h.1 (revPref_eq_of_both a t E F h h')

/-- **Existence of opportunity cost (Proposition 2.4).**
    If actor `a` performs some action `α` at time `t`, and a
    distinct action `β` is available at that time, then `β` is
    a *foregone* alternative — available but not realized. -/
theorem opportunity_cost
    (a : P.Actor) (t : P.Time) (α β : P.Action)
    (hα_acts : P.Acts a α t)
    (_hβ_avail : P.Avail a β t)
    (hαβ : α ≠ β) :
    ∃ F : P.EndE, P.EndOf β F ∧ ¬ P.Acts a β t := by
  obtain ⟨F, hβ_F⟩ := P.P3 β
  refine ⟨F, hβ_F, ?_⟩
  intro hβ_acts
  exact hαβ (P.C1 a t α β hα_acts hβ_acts)

end Praxeology

----------------------------------------------------------------
-- SECTION 5.  The Robinson Crusoe Model (nets-and-boats + E5)
----------------------------------------------------------------

/-! Concrete `Praxeology` instance: the three-period Crusoe economy
    of §3.6 of the Foundations paper, extended with the production
    enrichment E5 anticipated in future research.  Crusoe inhabits a
    small island with access to
    coastal and deep-sea resources. The choice menu grows
    monotonically as capital accumulates. The recipe-DAG is
    (Wood, Net, Boat at the higher orders; Plant, Fish, Tuna at the
    consumption layer):

        Wood ──BuildNet──→ Net ──ShoreFish───→ Fish      [order 1]
              │                 │                          consumable
              │                 └──DeepSeaFish─→ Tuna      [order 1]
              │                          ↑                  consumable
              └──BuildBoat──→ Boat ──────┘
                                                           [order 2]
                                                           [order 3]

        Forage ──→ Plant   (no input)                      [order 1]

    The fact that all axioms type-check means this is a genuine
    model of T_prx + E5. -/

inductive CrusoeActor : Type | crusoe
  deriving DecidableEq

inductive CrusoeAction : Type
  | forage | buildNet | shoreFish | buildBoat | deepSeaFish
  deriving DecidableEq

inductive CrusoeEnd : Type
  | subsist | capital | shoreCatch | deepCatch
  deriving DecidableEq

inductive CrusoeThing : Type
  | wood | net | boat | plant | fish | tuna
  deriving DecidableEq

inductive CrusoeTime : Type | t0 | t1 | t2
  deriving DecidableEq

open CrusoeActor CrusoeAction CrusoeEnd CrusoeThing CrusoeTime

/-- Time precedence: t0 < t1 < t2. -/
def CrusoeLt : CrusoeTime → CrusoeTime → Prop
  | t0, t1 => True
  | t0, t2 => True
  | t1, t2 => True
  | _,  _  => False

/-- Crusoe's actual choices:
    BuildNet at t0, BuildBoat at t1, DeepSeaFish at t2. -/
def CrusoeActs : CrusoeActor → CrusoeAction → CrusoeTime → Prop
  | crusoe, buildNet,    t0 => True
  | crusoe, buildBoat,   t1 => True
  | crusoe, deepSeaFish, t2 => True
  | _, _, _ => False

/-- Availability of actions at each time, encoding the
    monotone menu growth Γ₀ ⊂ Γ₁ ⊂ Γ₂.

      Γ₀ = {Forage, BuildNet}
      Γ₁ = {Forage, BuildNet, ShoreFish, BuildBoat}
      Γ₂ = {Forage, BuildNet, ShoreFish, BuildBoat, DeepSeaFish}
-/
def CrusoeAvail : CrusoeActor → CrusoeAction → CrusoeTime → Prop
  | crusoe, forage,      _  => True
  | crusoe, buildNet,    _  => True
  | crusoe, shoreFish,   t0 => False
  | crusoe, shoreFish,   _  => True
  | crusoe, buildBoat,   t0 => False
  | crusoe, buildBoat,   _  => True
  | crusoe, deepSeaFish, t2 => True
  | crusoe, deepSeaFish, _  => False

/-- Each action's end.  Note `buildNet` and `buildBoat` share
    the end `capital`: distinct means to the same Misesian want
    (possession of a productive tool). -/
def CrusoeEndOf : CrusoeAction → CrusoeEnd → Prop
  | forage,      subsist    => True
  | buildNet,    capital    => True
  | shoreFish,   shoreCatch => True
  | buildBoat,   capital    => True
  | deepSeaFish, deepCatch  => True
  | _, _ => False

/-- Use relation: which input thing each action requires.
    Forage takes no input (the immediate-subsistence channel);
    BuildNet uses wood; ShoreFish uses net; BuildBoat uses wood;
    DeepSeaFish uses both net and boat. -/
def CrusoeUse : CrusoeAction → CrusoeThing → Prop
  | buildNet,    wood => True
  | shoreFish,   net  => True
  | buildBoat,   wood => True
  | deepSeaFish, net  => True
  | deepSeaFish, boat => True
  | _, _ => False

/-- Result relation: each action produces exactly one thing.
    Forage→Plant, BuildNet→Net, ShoreFish→Fish, BuildBoat→Boat,
    DeepSeaFish→Tuna. -/
def CrusoeResult : CrusoeAction → CrusoeThing → Prop
  | forage,      plant => True
  | buildNet,    net   => True
  | shoreFish,   fish  => True
  | buildBoat,   boat  => True
  | deepSeaFish, tuna  => True
  | _, _ => False

/-- Consumable: only Plant, Fish, and Tuna directly satisfy wants. -/
def CrusoeConsumable : CrusoeThing → Prop
  | plant => True
  | fish  => True
  | tuna  => True
  | _     => False

/-- The Crusoe model is a praxeology with the production
    enrichment E5. Every base axiom is verified by Lean during the
    type-check of this `instance` block. -/
instance crusoeModel : Praxeology where
  Actor := CrusoeActor
  Action := CrusoeAction
  EndE  := CrusoeEnd
  Thing := CrusoeThing
  Time  := CrusoeTime
  Lt    := CrusoeLt
  Acts  := CrusoeActs
  Avail := CrusoeAvail
  EndOf := CrusoeEndOf
  Use   := CrusoeUse
  Result := CrusoeResult
  Consumable := CrusoeConsumable

  -- (T1) ¬ (t < t).
  T1_irrefl := by intro t h; cases t <;> exact h

  -- (T2) Transitivity.  Most cases have a False premise.
  T2_trans := by
    intro t s r h₁ h₂
    cases t <;> cases s <;> cases r <;>
      first | trivial | exact h₁.elim | exact h₂.elim

  -- (T3) Trichotomy.
  T3_trichot := by
    intro t s
    cases t <;> cases s <;>
      first
      | (exact Or.inl trivial)              -- t < s
      | (exact Or.inr (Or.inl rfl))         -- t = s
      | (exact Or.inr (Or.inr trivial))     -- s < t

  -- (T4) Some moment precedes another.  Witness: t0 < t1.
  T4_nontriv := ⟨t0, t1, trivial⟩

  -- (P1) Every actor has at least one available action at every time.
  -- Witness: Forage is always available.
  P1 := by
    intro a t
    refine ⟨forage, ?_⟩
    cases a; cases t <;> trivial

  -- (P2) Acted ⇒ available.
  P2 := by
    intro a α t h
    cases a; cases α <;> cases t <;>
      first | trivial | exact h.elim

  -- (P3) Every action has an end.
  P3 := by
    intro α
    cases α
    · exact ⟨subsist,    trivial⟩
    · exact ⟨capital,    trivial⟩
    · exact ⟨shoreCatch, trivial⟩
    · exact ⟨capital,    trivial⟩
    · exact ⟨deepCatch,  trivial⟩

  -- (P4) Each action has at most one end.
  P4 := by
    intro α E F hE hF
    cases α <;> cases E <;> cases F <;>
      first | rfl | exact hE.elim | exact hF.elim

  -- (P5) Distinct actions of one actor occur at distinct times.
  P5 := by
    intro a α β t s hα hβ hne
    cases a
    cases α <;> cases β <;> cases t <;> cases s <;>
      first
      | (exact (hne rfl).elim)        -- α = β contradicts hne
      | exact hα.elim                  -- premise hα = False
      | exact hβ.elim                  -- premise hβ = False
      | (intro h; cases h)             -- conclusion: t ≠ s by injection

  -- (C1) At most one action per actor per time.
  C1 := by
    intro a t α β hα hβ
    cases a
    cases t <;> cases α <;> cases β <;>
      first | rfl | exact hα.elim | exact hβ.elim

----------------------------------------------------------------
-- SECTION 6.  E5 verification: every CrusoeThing has finite Order
----------------------------------------------------------------

/-- **Theorem (PH2 for the Crusoe instance).**
    Every thing in the Crusoe model has a finite higher-order-goods
    rank.  Specifically:
      Plant, Fish, Tuna  : order 1 (consumable)
      Net, Boat          : order 2 (capital)
      Wood               : order 3 (raw material)
    This is the constructive verification that the production
    enrichment E5 is satisfied non-trivially on this model. -/
theorem CrusoeOrder_total : ∀ x : CrusoeThing,
    ∃ n, @Praxeology.Order crusoeModel x n := by
  intro x
  cases x
  ·  -- wood (order 3): Wood ──BuildNet──→ Net ──ShoreFish──→ Fish
    refine ⟨3, ?_⟩
    refine .step wood buildNet net 2 trivial trivial ?_
    refine .step net shoreFish fish 1 trivial trivial ?_
    exact .base fish trivial
  ·  -- net (order 2): Net ──ShoreFish──→ Fish
    refine ⟨2, ?_⟩
    refine .step net shoreFish fish 1 trivial trivial ?_
    exact .base fish trivial
  ·  -- boat (order 2): Boat ──DeepSeaFish──→ Tuna
    refine ⟨2, ?_⟩
    refine .step boat deepSeaFish tuna 1 trivial trivial ?_
    exact .base tuna trivial
  ·  -- plant (order 1): consumable
    exact ⟨1, .base plant trivial⟩
  ·  -- fish (order 1): consumable
    exact ⟨1, .base fish trivial⟩
  ·  -- tuna (order 1): consumable
    exact ⟨1, .base tuna trivial⟩

----------------------------------------------------------------
-- SECTION 7.  Sanity-check examples
----------------------------------------------------------------

/-! These `example`s use the theorems above on the Crusoe model.
    If they compile, the framework is working. -/

/-- Crusoe reveals `Capital ≻ Subsist` at time t0:
    he chose BuildNet (whose end is Capital) while Forage
    (whose end is Subsist) was available.  -/
example :
    @Praxeology.RevPref crusoeModel crusoe t0 capital subsist :=
  ⟨(by intro h; cases h), buildNet, forage, trivial, trivial,
   (by intro h; cases h), trivial, trivial⟩

/-- Crusoe does NOT reveal `Subsist ≻ Capital` at t0
    (asymmetry of revealed preference applied to the model above). -/
example :
    ¬ @Praxeology.RevPref crusoeModel crusoe t0 subsist capital :=
  @Praxeology.revPref_asymm crusoeModel crusoe t0 capital subsist
    ⟨(by intro h; cases h), buildNet, forage, trivial, trivial,
     (by intro h; cases h), trivial, trivial⟩

/-- At t0, Forage is a foregone alternative: Crusoe could have
    foraged but chose BuildNet instead. -/
example :
    ∃ F : CrusoeEnd, CrusoeEndOf forage F ∧ ¬ CrusoeActs crusoe forage t0 :=
  @Praxeology.opportunity_cost crusoeModel
    crusoe t0 buildNet forage
    (show CrusoeActs crusoe buildNet t0 from trivial)
    (show CrusoeAvail crusoe forage t0 from trivial)
    (by intro h; cases h)

/-- At t1, Crusoe reveals `Capital ≻ ShoreCatch`: he chose
    BuildBoat (whose end is Capital) over the available ShoreFish
    (whose end is ShoreCatch). This is a key revealed preference of
    the new running example — capital deepening chosen over
    immediate consumption. -/
example :
    @Praxeology.RevPref crusoeModel crusoe t1 capital shoreCatch :=
  ⟨(by intro h; cases h), buildBoat, shoreFish, trivial, trivial,
   (by intro h; cases h), trivial, trivial⟩

/-- At t2, Crusoe reveals `DeepCatch ≻ Capital`: he chose
    DeepSeaFish (consume the deep-sea catch) over BuildBoat
    (build another boat — also at end Capital). With both pieces
    of capital already in hand, realised consumption now outranks
    further deepening. -/
example :
    @Praxeology.RevPref crusoeModel crusoe t2 deepCatch capital :=
  ⟨(by intro h; cases h), deepSeaFish, buildBoat, trivial, trivial,
   (by intro h; cases h), trivial, trivial⟩

/-- E5 sanity: Wood is a 3rd-order good in the Crusoe instance.
    The witness chain is Wood ──BuildNet──→ Net ──ShoreFish──→ Fish
    with Fish consumable. -/
example : @Praxeology.Order crusoeModel wood 3 :=
  .step wood buildNet net 2 trivial trivial
    (.step net shoreFish fish 1 trivial trivial
      (.base fish trivial))

----------------------------------------------------------------
-- SECTION 8.  The (MU)-enrichment (§3.2)
----------------------------------------------------------------

/-- The `PraxeologyMU` class extends `Praxeology` with the
    additional primitives and axioms needed for the
    diminishing-marginal-utility theorem of §3.2.

    New primitives:
      * `Good`    : a new sort partitioning Things into
                    homogeneous classes.
      * `UnitOf`  : x is a unit of good g.
      * `Allot`   : actor a at time t allots unit x to end E
                    (the allocation schedule, distinct from
                    performance: see Section 2.4 of the paper).
      * `Pref`    : the revealed-preference order
                    `Pref a t E F` reads "E ≻ F by a at t".

    Axioms encoded here (the subset load-bearing for DMU and
    its corollary):
      * `Pref_comp`   : (O2) menu-comparability --- any two
                        distinct choice-relevant ends are
                        comparable.  Together with finiteness of
                        the choice menu (`rem:finiteness`) it
                        turns non-emptiness of the reduced served
                        set into existence and uniqueness of its
                        marginal end (Step 2 of `app:dmu_proof`).
      * `Pref_trans`  : (O3) transitivity of preference.
      * `Pref_asymm`  : strict-order convention; together with
                        transitivity gives irreflexivity.
      * `MU0_func`    : functionality half of (MU0) ---
                        each unit allots to at most one end.
      * `MU0_feas`    : feasibility half of (MU0) --- only
                        feasible cells are populated: an allotted
                        unit's good can serve the end (the
                        right-hand side is `Serviceable`,
                        inlined).  Underwrites
                        `lem:served_choice_relevant`.
      * `MU4_top`     : (MU4) preference-respecting allocation
                        (the served set is a top-segment of the
                        *g-serviceable* choice-relevant ends
                        under `Pref`).  The serviceability
                        qualifier confines the requirement to
                        ends within the good's reach: water
                        allotted to washing is not faulted
                        because hunger --- an end water cannot
                        serve --- ranks higher and goes unserved
                        by water.  Without the qualifier, any
                        model in which two goods alternate down
                        a single value scale would be excluded
                        outright (see `waterFishModel` below).

    The remaining (MU)-axioms ((MU2) menu-level fungibility,
    (MU3) scarcity awareness) are not invoked by the theorem or
    its corollary and are omitted here.  (MU2) and (MU3) are
    semantic and non-vacuity premises respectively; landing them
    in Lean is a routine extension. -/
class PraxeologyMU extends Praxeology where
  Good      : Type
  UnitOf    : Thing → Good → Prop
  Allot     : Actor → Time → Thing → EndE → Prop
  Pref      : Actor → Time → EndE → EndE → Prop

  Pref_comp  : ∀ (a : Actor) (t : Time) (E F : EndE),
                  E ≠ F →
                  (∃ α : Action, Avail a α t ∧ EndOf α E) →
                  (∃ β : Action, Avail a β t ∧ EndOf β F) →
                  Pref a t E F ∨ Pref a t F E
  Pref_trans : ∀ (a : Actor) (t : Time) (E F G : EndE),
                  Pref a t E F → Pref a t F G → Pref a t E G
  Pref_asymm : ∀ (a : Actor) (t : Time) (E F : EndE),
                  Pref a t E F → ¬ Pref a t F E

  MU0_func   : ∀ (a : Actor) (t : Time) (x : Thing) (E F : EndE),
                  Allot a t x E → Allot a t x F → E = F
  MU0_feas   : ∀ (a : Actor) (t : Time) (x : Thing) (g : Good) (E : EndE),
                  UnitOf x g → Allot a t x E →
                  (∃ (α : Action) (x' : Thing),
                     Avail a α t ∧ EndOf α E ∧ Use α x' ∧ UnitOf x' g)
  MU4_top    : ∀ (a : Actor) (t : Time) (g : Good) (E F : EndE),
                  (∃ x : Thing, UnitOf x g ∧ Allot a t x E) →
                  (∃ α : Action, Avail a α t ∧ EndOf α F) →
                  (∃ (α : Action) (x : Thing),
                     Avail a α t ∧ EndOf α F ∧ Use α x ∧ UnitOf x g) →
                  Pref a t F E →
                  (∃ x : Thing, UnitOf x g ∧ Allot a t x F)

----------------------------------------------------------------
-- SECTION 9.  Derived predicates of the (MU)-enrichment
----------------------------------------------------------------

namespace PraxeologyMU
variable [P : PraxeologyMU]

/-- `EndAt a t E` iff some action directed at `E` is available
    to `a` at `t`.  Definition `def:endat` (§2.1). -/
def EndAt (a : P.Actor) (t : P.Time) (E : P.EndE) : Prop :=
  ∃ α : P.Action, P.Avail a α t ∧ P.EndOf α E

/-- `Serviceable a t g E` iff some available action with end
    `E` uses some unit of `g`.  Definition `def:serviceable`. -/
def Serviceable (a : P.Actor) (t : P.Time)
    (g : P.Good) (E : P.EndE) : Prop :=
  ∃ α : P.Action, ∃ x : P.Thing,
    P.Avail a α t ∧ P.EndOf α E ∧ P.Use α x ∧ P.UnitOf x g

/-- `Served a t g E` iff some unit of `g` has been allotted to
    `E` at `(a,t)`.  Definition `def:served`. -/
def Served (a : P.Actor) (t : P.Time)
    (g : P.Good) (E : P.EndE) : Prop :=
  ∃ x : P.Thing, P.UnitOf x g ∧ P.Allot a t x E

/-- The reduced state: `ServedExcept a t g y E` is the served
    set obtained by deleting `y`'s allotment from the schedule.
    In Mises's "n vs n-1 units" language, this is the
    `(n-1)`-unit served set.  Definition `def:reduced_state`. -/
def ServedExcept (a : P.Actor) (t : P.Time) (g : P.Good)
    (y : P.Thing) (E : P.EndE) : Prop :=
  ∃ x : P.Thing, P.UnitOf x g ∧ x ≠ y ∧ P.Allot a t x E

/-- Dropping the `x ≠ y` restriction: a reduced-served end is
    served.  (The "reduced case" sentence of
    `lem:served_choice_relevant`.) -/
theorem servedExcept_served
    (a : P.Actor) (t : P.Time) (g : P.Good)
    (y : P.Thing) (E : P.EndE)
    (h : ServedExcept a t g y E) : Served a t g E := by
  obtain ⟨x, hxUnit, _, hxAllot⟩ := h
  exact ⟨x, hxUnit, hxAllot⟩

/-- **Lemma (Served ends are choice-relevant)** ---
    Lemma `lem:served_choice_relevant`.

    If some unit of `g` is allotted to `E` at `(a,t)`, then `E`
    is choice-relevant: some available action aims at `E`.

    *Proof.*  The witnessing allotment is a populated cell of the
    schedule; by (MU0) feasibility its end is `g`-serviceable,
    and `Serviceable` (Definition `def:serviceable`) exhibits an
    available action with end `E`, i.e. `EndAt a t E`. -/
theorem served_choice_relevant
    (a : P.Actor) (t : P.Time) (g : P.Good) (E : P.EndE)
    (h : Served a t g E) : EndAt a t E := by
  obtain ⟨x, hxUnit, hxAllot⟩ := h
  obtain ⟨α, _, hAvail, hEnd, _, _⟩ := P.MU0_feas a t x g E hxUnit hxAllot
  exact ⟨α, hAvail, hEnd⟩

end PraxeologyMU

----------------------------------------------------------------
-- SECTION 10.  Diminishing Marginal Utility
----------------------------------------------------------------

/-- **Helper (minimum of a finite set under a strict total
    order).**  If a predicate `S` is non-empty on a list `l` and
    the relation `R` is transitive and total on `S`, then `S` has
    an `R`-minimal element among the members of `l` (an element
    `m` with `R F m ∨ F = m` for every `S`-member `F` of `l`).

    This is the only place finiteness enters: it is the Lean
    counterpart of "a non-empty finite subset of a strict total
    order has a unique minimal element" in Step 2 of
    `app:dmu_proof`, with the finiteness of the choice menu
    (`rem:finiteness`) supplied as the covering list `l`.  Stated
    for an arbitrary type so it stays independent of the
    praxeological signature. -/
private theorem exists_min_on_list {α : Type} {R : α → α → Prop}
    {S : α → Prop}
    (Rtrans : ∀ {x y z : α}, R x y → R y z → R x z)
    (comp : ∀ {x y : α}, S x → S y → x ≠ y → R x y ∨ R y x) :
    ∀ l : List α, (∃ x, S x ∧ x ∈ l) →
      ∃ m, S m ∧ ∀ F, S F → F ∈ l → R F m ∨ F = m := by
  intro l
  induction l with
  | nil =>
    intro ⟨_, _, hx⟩
    cases hx
  | cons a l ih =>
    intro ⟨x, hSx, hxmem⟩
    by_cases hSa : S a
    ·  -- The head satisfies S.  Does the tail contribute?
      by_cases hl : ∃ z, S z ∧ z ∈ l
      ·  -- Take the tail's minimum m and compare it with a.
        obtain ⟨m, hSm, hmin⟩ := ih hl
        by_cases ham : a = m
        ·  -- a coincides with the tail minimum.
          subst ham
          refine ⟨a, hSa, ?_⟩
          intro F hSF hF
          rcases List.mem_cons.mp hF with rfl | hF'
          · exact Or.inr rfl
          · exact hmin F hSF hF'
        · rcases comp hSa hSm ham with hRam | hRma
          ·  -- a ≻ m: the tail minimum survives.
            refine ⟨m, hSm, ?_⟩
            intro F hSF hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact Or.inl hRam
            · exact hmin F hSF hF'
          ·  -- m ≻ a: the head becomes the new minimum
             -- (transitivity pushes everything above a).
            refine ⟨a, hSa, ?_⟩
            intro F hSF hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact Or.inr rfl
            · rcases hmin F hSF hF' with hFm | rfl
              · exact Or.inl (Rtrans hFm hRma)
              · exact Or.inl hRma
      ·  -- The head is the only S-member.
        refine ⟨a, hSa, ?_⟩
        intro F hSF hF
        rcases List.mem_cons.mp hF with rfl | hF'
        · exact Or.inr rfl
        · exact absurd ⟨F, hSF, hF'⟩ hl
    ·  -- The head fails S: the witness lives in the tail.
      have hxl : x ∈ l := by
        rcases List.mem_cons.mp hxmem with rfl | h
        · exact absurd hSx hSa
        · exact h
      obtain ⟨m, hSm, hmin⟩ := ih ⟨x, hSx, hxl⟩
      refine ⟨m, hSm, ?_⟩
      intro F hSF hF
      rcases List.mem_cons.mp hF with rfl | hF'
      · exact absurd hSF hSa
      · exact hmin F hSF hF'

namespace PraxeologyMU
variable [P : PraxeologyMU]

/-- **Theorem (Diminishing marginal utility)** ---
    Theorem `thm:DMU`, in the paper's tightened form: the
    reduced marginal end `E*` is *derived*, not assumed.

    Let `y` be a unit of good `g` allotted at `(a,t)` to a
    choice-relevant end `E`.  Suppose:
      (i)   *Uniqueness on E* --- no other unit of `g` is
            allotted to `E`.
      (ii)  *Marginality of E* --- `E` is the least-preferred
            end currently served by `g` at `(a,t)`
            (Definition `def:marginal_end`).
      (iii) *Non-emptiness of the reduced supply* --- some end
            other than `E` is served by `g` at `(a,t)`
            (Mises's implicit `n ≥ 2`).
    Then the marginal end `E*` of the reduced served set
    `ServedExcept a t g y` exists, is unique, and satisfies
    `E* ≻ E`.

    Finiteness of the choice menu (`rem:finiteness`) enters as
    the hypothesis pair `menu`/`hmenu`: a list of ends covering
    the choice-relevant ends at `(a,t)`.  (No finiteness is
    assumed of the sort `EndE` itself, matching the remark.)

    The proof matches Steps 1–3 of the appendix proof
    `app:dmu_proof`: besides the hypotheses it consumes
    `lem:served_choice_relevant`, the functionality half of
    (MU0) (which turns non-emptiness (iii) into existence of
    `E*`), and (O2)/(O3) comparability and transitivity on the
    choice menu.  (MU4) is not invoked --- it is deductively
    engaged only in `DMU_structure` below. -/
theorem DMU
    (a : P.Actor) (t : P.Time) (g : P.Good)
    (y : P.Thing) (E : P.EndE)
    -- Setup of the theorem statement
    (_hyUnit : P.UnitOf y g)
    (hyAllot : P.Allot a t y E)
    (_hyEndAt : EndAt a t E)
    -- Finiteness of the choice menu (rem:finiteness)
    (menu : List P.EndE)
    (hmenu : ∀ F : P.EndE, EndAt a t F → F ∈ menu)
    -- (i) Uniqueness on E
    (uniq : ∀ x : P.Thing,
              P.UnitOf x g → P.Allot a t x E → x = y)
    -- (ii) Marginality of E in the full state
    (marg : ∀ F : P.EndE,
              Served a t g F → P.Pref a t F E ∨ F = E)
    -- (iii) Non-emptiness of the reduced supply
    (nonempty : ∃ F : P.EndE, F ≠ E ∧ Served a t g F)
    : ∃ E_star : P.EndE,
        -- E* is the marginal end of the reduced served set ...
        (ServedExcept a t g y E_star ∧
          ∀ F : P.EndE, ServedExcept a t g y F →
            P.Pref a t F E_star ∨ F = E_star) ∧
        -- ... it is unique with that property ...
        (∀ E' : P.EndE,
            ServedExcept a t g y E' →
            (∀ F : P.EndE, ServedExcept a t g y F →
              P.Pref a t F E' ∨ F = E') →
            E' = E_star) ∧
        -- ... and DMU proper: E* ≻ E.
        P.Pref a t E_star E := by
  -- Step 1: every end of the reduced served set differs from E
  -- (by uniqueness (i)) and hence sits strictly above E (by
  -- marginality (ii)).
  have step1 : ∀ F : P.EndE,
      ServedExcept a t g y F → P.Pref a t F E := by
    intro F hF
    obtain ⟨x, hxUnit, hxNe, hxAllot⟩ := hF
    have hFne : F ≠ E := by
      intro heq
      rw [heq] at hxAllot
      exact hxNe (uniq x hxUnit hxAllot)
    rcases marg F ⟨x, hxUnit, hxAllot⟩ with h | h
    · exact h
    · exact absurd h hFne
  -- Step 2a: the reduced served set is non-empty.  The witness
  -- unit for (iii) cannot be y: y's cell is E by the theorem
  -- premise, and (MU0)-functionality forbids a second cell.
  obtain ⟨F₀, hF₀ne, x₀, hx₀Unit, hx₀Allot⟩ := nonempty
  have hx₀y : x₀ ≠ y := by
    intro h
    rw [h] at hx₀Allot
    exact hF₀ne (P.MU0_func a t y F₀ E hx₀Allot hyAllot)
  have hF₀red : ServedExcept a t g y F₀ := ⟨x₀, hx₀Unit, hx₀y, hx₀Allot⟩
  -- Step 2b: reduced-served ends are choice-relevant
  -- (lem:served_choice_relevant), hence lie in the finite menu,
  -- on which Pref is a strict total order by (O2)/(O3).
  have hcover : ∀ F : P.EndE, ServedExcept a t g y F → F ∈ menu :=
    fun F hF =>
      hmenu F (served_choice_relevant a t g F (servedExcept_served a t g y F hF))
  have hcomp : ∀ {F G : P.EndE},
      ServedExcept a t g y F → ServedExcept a t g y G → F ≠ G →
      P.Pref a t F G ∨ P.Pref a t G F :=
    fun hF hG hne =>
      P.Pref_comp a t _ _ hne
        (served_choice_relevant a t g _ (servedExcept_served a t g y _ hF))
        (served_choice_relevant a t g _ (servedExcept_served a t g y _ hG))
  -- Extract the minimum E* of the reduced served set.
  obtain ⟨E_star, hSE, hminOn⟩ :=
    exists_min_on_list
      (R := fun F G => P.Pref a t F G)
      (S := fun F => ServedExcept a t g y F)
      (fun h₁ h₂ => P.Pref_trans a t _ _ _ h₁ h₂) hcomp
      menu ⟨F₀, hF₀red, hcover F₀ hF₀red⟩
  have hmin : ∀ F : P.EndE, ServedExcept a t g y F →
      P.Pref a t F E_star ∨ F = E_star :=
    fun F hF => hminOn F hF (hcover F hF)
  -- Assemble: marginality of E*, uniqueness (via comparability
  -- and asymmetry), and Step 3: E* ≻ E from Step 1.
  refine ⟨E_star, ⟨hSE, hmin⟩, ?_, step1 E_star hSE⟩
  intro E' hSE' hmin'
  rcases hmin E' hSE' with h | h
  · rcases hmin' E_star hSE with h' | h'
    · exact absurd h' (P.Pref_asymm a t E' E_star h)
    · exact h'.symm
  · exact h

/-- **Corollary (Structure preservation under marginal removal)**
    --- Corollary `cor:dmu_structure`.

    Under the hypotheses of `DMU`, the reduced served set
    `ServedExcept a t g y` is itself a top-segment of the
    *g-serviceable* choice-relevant ends under `Pref`, i.e.
    (MU4) continues to hold for the "y-removed" allotment.

    This *does* use (MU0)-functionality and (MU4)-top-segment
    on the full state, plus `Pref_asymm`. -/
theorem DMU_structure
    (a : P.Actor) (t : P.Time) (g : P.Good)
    (y : P.Thing) (E : P.EndE)
    (_hyUnit  : P.UnitOf y g)
    (hyAllot  : P.Allot a t y E)
    (uniq     : ∀ x : P.Thing,
                  P.UnitOf x g → P.Allot a t x E → x = y)
    (marg     : ∀ F : P.EndE,
                  Served a t g F → P.Pref a t F E ∨ F = E)
    : ∀ (F' G : P.EndE),
        ServedExcept a t g y F' →
        EndAt a t G →
        Serviceable a t g G →
        P.Pref a t G F' →
        ServedExcept a t g y G := by
  intro F' G hF' hG hGserv hpref
  -- Unpack F' ∈ ServedExcept y, then F' is also Served.
  obtain ⟨xF, hxFUnit, hxFNe, hxFAllot⟩ := hF'
  have hF'Served : Served a t g F' := ⟨xF, hxFUnit, hxFAllot⟩
  -- F' ≠ E: if F' = E then uniq forces xF = y, contradicting hxFNe.
  have hF'NotE : F' ≠ E := by
    intro heq
    rw [heq] at hxFAllot
    exact hxFNe (uniq xF hxFUnit hxFAllot)
  -- F' ≻ E from marginality applied to F'.
  have hF'_E : P.Pref a t F' E := by
    rcases marg F' hF'Served with h | h
    · exact h
    · exact absurd h hF'NotE
  -- (MU4)-top-segment: G ≻ F', G g-serviceable, and F' served
  -- implies G served.
  have hGServed : Served a t g G :=
    P.MU4_top a t g F' G hF'Served hG hGserv hpref
  obtain ⟨z, hzUnit, hzAllot⟩ := hGServed
  -- Split on z = y.
  by_cases hzy : z = y
  ·  -- If z = y, then G = E by (MU0)-functionality, then
     -- hpref : Pref a t E F' contradicts hF'_E : Pref a t F' E
     -- via Pref_asymm.
    rw [hzy] at hzAllot
    have hGE : G = E := P.MU0_func a t y G E hzAllot hyAllot
    rw [hGE] at hpref
    exact absurd hpref (P.Pref_asymm a t F' E hF'_E)
  ·  -- z ≠ y: G is in ServedExcept y.
    exact ⟨z, hzUnit, hzy, hzAllot⟩

end PraxeologyMU

----------------------------------------------------------------
-- SECTION 11.  The two-good water/fish model (MU4 satisfiability)
----------------------------------------------------------------

/-! Concrete `PraxeologyMU` instance: the "two-good allotment
    schedule" Crusoe box accompanying (MU4) in §3.2 of the
    Foundations paper.  Robinson holds four units w1–w4 of the
    good Water and three units f1–f3 of the good Fish, with six
    choice-relevant ends ranked

        Drink ≻ Eat ≻ Cook ≻ Store ≻ Wash ≻ Garden.

    Water can serve Drink, Cook, Wash, Garden; fish can serve
    Eat, Store.  The allotment schedule (one cell per unit):

        w1 → Drink          f1 → Eat
        w2 → Cook           f2 → Eat
        w3 → Cook           f3 → Store
        w4 → Wash           (Garden unserved — an (MU3) witness)

    The two goods *alternate* down the single value scale —
    water, fish, water, fish, water — which is exactly the case
    the unrelativized (MU4) excluded: water serving Cook would
    have been faulted for Eat ≻ Cook going unserved by water,
    although water cannot serve Eat.  Lean's acceptance of this
    instance is a constructive satisfiability proof of the
    corrected, relativized axiom class on a multi-good model;
    the `example` after the instance verifies that the *old*
    unrelativized (MU4) is genuinely false here. -/

inductive WFActor : Type | robinson
  deriving DecidableEq

/-- One action per (good, serviceable end) pair. -/
inductive WFAction : Type
  | drinkWater | eatFish | cookWithWater | storeFish
  | washWithWater | waterGarden
  deriving DecidableEq

inductive WFEnd : Type
  | drink | eat | cook | store | wash | garden
  deriving DecidableEq

inductive WFThing : Type
  | w1 | w2 | w3 | w4 | f1 | f2 | f3
  deriving DecidableEq

inductive WFTime : Type | s0 | s1
  deriving DecidableEq

inductive WFGood : Type | water | fishG
  deriving DecidableEq

/-- Time precedence: s0 < s1. -/
def WFLt : WFTime → WFTime → Prop
  | .s0, .s1 => True
  | _,   _   => False

/-- Robinson's chosen history: he drinks at s0 (the top-ranked
    end), nothing recorded at s1. -/
def WFActs : WFActor → WFAction → WFTime → Prop
  | _, .drinkWater, .s0 => True
  | _, _, _ => False

/-- All six actions are available at all times: the whole value
    scale is choice-relevant throughout. -/
def WFAvail : WFActor → WFAction → WFTime → Prop :=
  fun _ _ _ => True

/-- Each action's end. -/
def WFEndOf : WFAction → WFEnd → Prop
  | .drinkWater,    .drink  => True
  | .eatFish,       .eat    => True
  | .cookWithWater, .cook   => True
  | .storeFish,     .store  => True
  | .washWithWater, .wash   => True
  | .waterGarden,   .garden => True
  | _, _ => False

/-- Use relation: each action employs one representative unit of
    its good (one witness suffices for `Serviceable`; the
    menu-level fungibility axiom (MU2) is not part of the Lean
    class). -/
def WFUse : WFAction → WFThing → Prop
  | .drinkWater,    .w1 => True
  | .cookWithWater, .w2 => True
  | .washWithWater, .w4 => True
  | .waterGarden,   .w1 => True
  | .eatFish,       .f1 => True
  | .storeFish,     .f3 => True
  | _, _ => False

/-- Units of the two goods. -/
def WFUnitOf : WFThing → WFGood → Prop
  | .w1, .water | .w2, .water | .w3, .water | .w4, .water => True
  | .f1, .fishG | .f2, .fishG | .f3, .fishG => True
  | _, _ => False

/-- The allotment schedule of the Crusoe box: seven cells,
    constant over time.  Eat and Cook are multi-unit ends
    (two cells each); Garden is unserved. -/
def WFAllot : WFActor → WFTime → WFThing → WFEnd → Prop
  | _, _, .w1, .drink => True
  | _, _, .w2, .cook  => True
  | _, _, .w3, .cook  => True
  | _, _, .w4, .wash  => True
  | _, _, .f1, .eat   => True
  | _, _, .f2, .eat   => True
  | _, _, .f3, .store => True
  | _, _, _, _ => False

/-- Rank on the single value scale (0 = most preferred):
    Drink ≻ Eat ≻ Cook ≻ Store ≻ Wash ≻ Garden. -/
def WFRank : WFEnd → Nat
  | .drink  => 0
  | .eat    => 1
  | .cook   => 2
  | .store  => 3
  | .wash   => 4
  | .garden => 5

/-- The two-good water/fish model satisfies every axiom of
    `PraxeologyMU` — including the corrected, relativized (MU4).
    Every axiom is verified by Lean during the type-check of
    this `instance` block. -/
instance waterFishModel : PraxeologyMU where
  Actor  := WFActor
  Action := WFAction
  EndE   := WFEnd
  Thing  := WFThing
  Time   := WFTime
  Lt     := WFLt
  Acts   := WFActs
  Avail  := WFAvail
  EndOf  := WFEndOf
  Use    := WFUse
  -- The production enrichment is idle in this instance: nothing
  -- is produced, and every unit directly satisfies wants.
  Result := fun _ _ => False
  Consumable := fun _ => True

  T1_irrefl := by intro t h; cases t <;> exact h
  T2_trans := by
    intro t s r h₁ h₂
    cases t <;> cases s <;> cases r <;>
      first | trivial | exact h₁.elim | exact h₂.elim
  T3_trichot := by
    intro t s
    cases t <;> cases s <;>
      first
      | (exact Or.inl trivial)
      | (exact Or.inr (Or.inl rfl))
      | (exact Or.inr (Or.inr trivial))
  T4_nontriv := ⟨.s0, .s1, trivial⟩

  -- (P1) Everything is always available.
  P1 := fun _ _ => ⟨.drinkWater, trivial⟩
  P2 := fun _ _ _ _ => trivial
  P3 := by
    intro α
    cases α
    · exact ⟨.drink,  trivial⟩
    · exact ⟨.eat,    trivial⟩
    · exact ⟨.cook,   trivial⟩
    · exact ⟨.store,  trivial⟩
    · exact ⟨.wash,   trivial⟩
    · exact ⟨.garden, trivial⟩
  P4 := by
    intro α E F hE hF
    cases α <;> cases E <;> cases F <;>
      first | rfl | exact hE.elim | exact hF.elim
  -- (P5) Only one action is ever performed, so the premises pin
  -- α = β = drinkWater and the α ≠ β hypothesis closes each case.
  P5 := by
    intro a α β t s hα hβ hne
    cases α <;> cases β <;> cases t <;> cases s <;>
      first | exact (hne rfl).elim | exact hα.elim | exact hβ.elim
  C1 := by
    intro a t α β hα hβ
    cases t <;> cases α <;> cases β <;>
      first | rfl | exact hα.elim | exact hβ.elim

  Good   := WFGood
  UnitOf := WFUnitOf
  Allot  := WFAllot
  -- The single value scale, read off the rank function.
  Pref   := fun _ _ E F => WFRank E < WFRank F

  -- (O2) Any two distinct ends are rank-comparable.
  Pref_comp := by
    intro a t E F hne _ _
    cases E <;> cases F <;>
      first
      | exact absurd rfl hne
      | exact Or.inl (by decide)
      | exact Or.inr (by decide)
  Pref_trans := fun _ _ _ _ _ h₁ h₂ => Nat.lt_trans h₁ h₂
  Pref_asymm := by
    intro a t E F h h'
    omega

  -- (MU0) functionality: each unit occupies at most one cell.
  MU0_func := by
    intro a t x E F hE hF
    cases x <;> cases E <;> cases F <;>
      first | rfl | exact hE.elim | exact hF.elim
  -- (MU0) feasibility: every populated cell pairs a unit with an
  -- end its good can serve; the witnesses are the six actions.
  MU0_feas := by
    intro a t x g E hUnit hAllot
    cases x <;> cases g <;> cases E <;>
      first
      | exact hUnit.elim
      | exact hAllot.elim
      | exact ⟨.drinkWater,    .w1, trivial, trivial, trivial, trivial⟩
      | exact ⟨.eatFish,       .f1, trivial, trivial, trivial, trivial⟩
      | exact ⟨.cookWithWater, .w2, trivial, trivial, trivial, trivial⟩
      | exact ⟨.storeFish,     .f3, trivial, trivial, trivial, trivial⟩
      | exact ⟨.washWithWater, .w4, trivial, trivial, trivial, trivial⟩
  -- (MU4) relativized top-segment, verified good by good:
  --   water's served set {Drink, Cook, Wash} is a top-segment of
  --   the water-serviceable ends {Drink, Cook, Wash, Garden};
  --   fish's served set {Eat, Store} exhausts the
  --   fish-serviceable ends {Eat, Store}.
  -- Served goals are closed by exhibiting the allotted unit;
  -- non-serviceable F is refuted from the Serviceable premise;
  -- for (water, Garden) the Pref premise is refuted (Garden is
  -- bottom-ranked) once the Served premise pins E.
  MU4_top := by
    intro a t g E F hServed _hEndAt hServiceable hPref
    cases g <;> cases F <;>
      first
      | exact ⟨.w1, trivial, trivial⟩
      | exact ⟨.w2, trivial, trivial⟩
      | exact ⟨.w4, trivial, trivial⟩
      | exact ⟨.f1, trivial, trivial⟩
      | exact ⟨.f3, trivial, trivial⟩
      | (obtain ⟨α, x, _, hEnd, hUse, hUnit⟩ := hServiceable
         cases α <;> cases x <;>
           first | exact hEnd.elim | exact hUse.elim | exact hUnit.elim)
      | (obtain ⟨z, hzUnit, hzAllot⟩ := hServed
         cases E <;> cases z <;>
           first
           | exact hzUnit.elim
           | exact hzAllot.elim
           | exact absurd hPref (by decide))

/-- **The old, unrelativized (MU4) fails on the two-good model.**
    Instantiated at `g = water`, `E = Cook`, `F = Eat`: water
    serves Cook, Eat is choice-relevant and higher-ranked
    (Eat ≻ Cook), yet no unit of water is — or, by (MU0)
    feasibility, could be — allotted to Eat.  This is review
    finding #11: the quantifier of the original (MU4) ranged
    over *all* higher-ranked choice-relevant ends instead of the
    `g`-serviceable ones, so it excluded every model whose goods
    alternate down one value scale.  The relativized `MU4_top`
    of `waterFishModel` type-checks; this `example` shows the
    relativization is not vacuous but necessary. -/
example :
    ¬ (∀ (E F : WFEnd),
        (∃ x : WFThing, WFUnitOf x .water ∧
           WFAllot .robinson .s0 x E) →
        (∃ α : WFAction, WFAvail .robinson α .s0 ∧ WFEndOf α F) →
        WFRank F < WFRank E →
        (∃ x : WFThing, WFUnitOf x .water ∧
           WFAllot .robinson .s0 x F)) := by
  intro h
  -- Apply the unrelativized axiom to E = Cook (served by w2),
  -- F = Eat (choice-relevant via eatFish, and Eat ≻ Cook).
  obtain ⟨x, hUnit, hAllot⟩ :=
    h .cook .eat ⟨.w2, trivial, trivial⟩
      ⟨.eatFish, trivial, trivial⟩ (by decide)
  -- But no unit of water is allotted to Eat.
  cases x <;> first | exact hUnit.elim | exact hAllot.elim

/-- **DMU applied in the two-good model.**  Water's marginal end
    is Wash, served uniquely by w4.  Removing w4 leaves the
    reduced water-served set {Drink, Cook}; the theorem derives
    its marginal end E* and concludes E* ≻ Wash (in fact
    E* = Cook).  All three hypotheses and the finite menu are
    discharged by case analysis. -/
example :
    ∃ E_star : WFEnd,
      @PraxeologyMU.ServedExcept waterFishModel
        .robinson .s0 .water .w4 E_star ∧
      WFRank E_star < WFRank .wash := by
  obtain ⟨E_star, ⟨hServed, _⟩, _, hPref⟩ :=
    @PraxeologyMU.DMU waterFishModel .robinson .s0 .water .w4 .wash
      -- setup: w4 is a unit of water, allotted to Wash,
      -- and Wash is choice-relevant
      trivial trivial ⟨.washWithWater, trivial, trivial⟩
      -- finiteness: the six-end menu covers the choice-relevant ends
      [.drink, .eat, .cook, .store, .wash, .garden]
      (by intro F _
          cases F
          · exact .head _
          · exact .tail _ (.head _)
          · exact .tail _ (.tail _ (.head _))
          · exact .tail _ (.tail _ (.tail _ (.head _)))
          · exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
          · exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
      -- (i) uniqueness: only w4 is allotted to Wash
      (by intro x h₁ h₂
          cases x <;> first | rfl | exact h₁.elim | exact h₂.elim)
      -- (ii) marginality: every water-served end is ≻ Wash or = Wash
      (by intro F hF
          obtain ⟨x, hUnit, hAllot⟩ := hF
          cases F <;> cases x <;>
            first
            | exact hUnit.elim
            | exact hAllot.elim
            | exact Or.inl (show WFRank _ < WFRank _ by decide)
            | exact Or.inr rfl)
      -- (iii) non-emptiness: Cook ≠ Wash is also water-served (by w2)
      ⟨.cook, (by intro h; cases h), .w2, trivial, trivial⟩
  exact ⟨E_star, hServed, hPref⟩

----------------------------------------------------------------
-- SECTION 12.  The full base theory T_prx  (Layers 1 + 2 + 3)
----------------------------------------------------------------

/-! The class `Praxeology` above encodes the *action core* of the
    Foundations paper — the fragment (T1)–(T4), (P1)–(P5), (C1)
    that the paper's Appendix A calls "the encoded core."  The
    full base theory adds the remaining time axioms ((T0) first
    moment, (T5) irreversibility, (T6) discreteness), free-good
    exclusion (P6), the scarcity anchor (S1), and Layer 2: the
    valuational primitive `Pref` — the actor's scale of values —
    together with the grounding axiom (O0) and the order axioms
    (O1)–(O4), per the paper's §2.3 redesign.

    (T6) gives every moment a successor, so the full theory has
    **no finite models**: the three-period Crusoe instance above
    cannot witness it.  Section 13 provides the ℕ-time witness. -/

class PraxeologyFull extends Praxeology where
  /-- Layer-2 valuational primitive: the actor's scale of values
      `E ≻ᵗₐ F`.  Primitive in the language, epistemically hidden;
      grounded in the revealed record by (O0). -/
  Pref : Actor → Time → EndE → EndE → Prop

  -- Remaining TIME-ORDER axioms (T0, T5, T6)
  T0_first : ∃ t₀ : Time, ∀ t : Time, t₀ = t ∨ Lt t₀ t
  T5_irrev : ∀ t s : Time, Lt t s → ¬ Lt s t
  T6_succ  : ∀ t : Time, ∃ s : Time,
               Lt t s ∧ ¬ ∃ r : Time, Lt t r ∧ Lt r s

  -- (P6) Free-good exclusion: every employed thing has, at some
  -- time, an available-but-unperformed employing action.
  P6 : ∀ (a : Actor) (t : Time) (α : Action) (x : Thing),
       Acts a α t → Use α x →
       ∃ (β : Action) (s : Time),
         Avail a β s ∧ Use β x ∧ ¬ Acts a β s

  -- (S1) Existence of scarcity: a genuine resource conflict.
  S1 : ∃ (a : Actor) (t : Time) (α β : Action) (x : Thing),
       α ≠ β ∧ Avail a α t ∧ Avail a β t ∧ Use α x ∧ Use β x

  -- LAYER-2 AXIOMS (O0)–(O4).  (O0) is stated with the record
  -- definition inlined (definitionally equal to `RevPref`).
  O0_grounding : ∀ (a : Actor) (t : Time) (E F : EndE),
       (E ≠ F ∧ ∃ α β : Action,
         Acts a α t ∧ Avail a β t ∧ α ≠ β ∧
         EndOf α E ∧ EndOf β F) →
       Pref a t E F
  O1_always : ∀ (a : Actor) (t : Time), ∃ α : Action, Acts a α t
  O2_total : ∀ (a : Actor) (t : Time) (E F : EndE), E ≠ F →
       (∃ α : Action, Avail a α t ∧ EndOf α E) →
       (∃ β : Action, Avail a β t ∧ EndOf β F) →
       Pref a t E F ∨ Pref a t F E
  O3_trans : ∀ (a : Actor) (t : Time) (E F G : EndE),
       Pref a t E F → Pref a t F G → Pref a t E G
  O4_asymm : ∀ (a : Actor) (t : Time) (E F : EndE),
       Pref a t E F → ¬ Pref a t F E

/-- **The chosen end tops the scale (`prop:chosen_max`).**
    The performed action's end outranks every other available end:
    the record is a star from the realised end, and (O0) lifts the
    star into the primitive order.  Uniqueness of the maximum is
    immediate from (O4). -/
theorem PraxeologyFull.chosen_end_tops_scale [P : PraxeologyFull]
    (a : P.Actor) (t : P.Time) (α : P.Action) (Ehat F : P.EndE)
    (hact : P.Acts a α t) (hend : P.EndOf α Ehat) (hne : F ≠ Ehat)
    (β : P.Action) (hav : P.Avail a β t) (hβF : P.EndOf β F) :
    P.Pref a t Ehat F := by
  have hαβ : α ≠ β := by
    intro h
    exact hne (P.P4 α F Ehat (h ▸ hβF) hend)
  exact P.O0_grounding a t Ehat F
    ⟨fun h => hne h.symm, α, β, hact, hav, hαβ, hend, hβF⟩

----------------------------------------------------------------
-- SECTION 13.  The ℕ-time Crusoe model: consistency of the
--              full base theory
----------------------------------------------------------------

/-! (T6) has no finite models, so the witness needs `Time := ℕ`.
    This folds the paper's state diagram into an infinite history,
    making the "walk the diagram for as many rounds as you want"
    reading a machine-checked consistency proof of the FULL base
    theory.  Two design constraints are respected:

    * **Non-greedy history.**  After building the net (t = 0) and
      the boat (t = 1), Crusoe alternates deep-sea fishing (even
      t ≥ 2) with shore fishing (odd t ≥ 3).  A greedy "always
      deep-sea" history would falsify (P6) for the boat: the only
      boat-using action would never be available-but-unperformed.

    * **Orders co-vary with the history.**  The preference ranks
      flip with the parity of t, so the chosen end always tops the
      scale and (O0) holds at every moment.  Preference reversal
      across time is licensed by `rem:constancy`. -/

namespace NatCrusoe

open CrusoeActor CrusoeAction CrusoeEnd CrusoeThing

/-- The infinite, non-greedy history. -/
def act : Nat → CrusoeAction
  | 0     => buildNet
  | 1     => buildBoat
  | n + 2 => if n % 2 = 0 then deepSeaFish else shoreFish

def NatActs : CrusoeActor → CrusoeAction → Nat → Prop :=
  fun _ α t => α = act t

/-- Menus by capital epoch: Forage and BuildNet always (Q₀);
    ShoreFish and BuildBoat from t = 1 (net in hand, Q₁);
    DeepSeaFish from t = 2 (boat in hand, Q₂). -/
def NatAvail : CrusoeActor → CrusoeAction → Nat → Prop :=
  fun _ α t =>
    match α with
    | forage      => True
    | buildNet    => True
    | shoreFish   => 1 ≤ t
    | buildBoat   => 1 ≤ t
    | deepSeaFish => 2 ≤ t

/-- Preference ranks, lower = more preferred: capital-formation
    phase (t = 0, 1), deep-sea days (even t ≥ 2), shore days
    (odd t ≥ 3). -/
def rankEarly : CrusoeEnd → Nat
  | capital => 0 | shoreCatch => 1 | subsist => 2 | deepCatch => 3
def rankEven : CrusoeEnd → Nat
  | deepCatch => 0 | shoreCatch => 1 | subsist => 2 | capital => 3
def rankOdd : CrusoeEnd → Nat
  | shoreCatch => 0 | deepCatch => 1 | subsist => 2 | capital => 3

def rank : Nat → CrusoeEnd → Nat
  | 0     => rankEarly
  | 1     => rankEarly
  | n + 2 => if n % 2 = 0 then rankEven else rankOdd

def NatPref : CrusoeActor → Nat → CrusoeEnd → CrusoeEnd → Prop :=
  fun _ t E F => rank t E < rank t F

/-- Each per-phase rank function is injective … -/
theorem rankEarly_inj : ∀ E F, rankEarly E = rankEarly F → E = F := by
  intro E F h
  cases E <;> cases F <;> first | rfl | exact absurd h (by decide)
theorem rankEven_inj : ∀ E F, rankEven E = rankEven F → E = F := by
  intro E F h
  cases E <;> cases F <;> first | rfl | exact absurd h (by decide)
theorem rankOdd_inj : ∀ E F, rankOdd E = rankOdd F → E = F := by
  intro E F h
  cases E <;> cases F <;> first | rfl | exact absurd h (by decide)

/-- … hence `rank t` is injective at every time. -/
theorem rank_inj : ∀ (t : Nat) (E F : CrusoeEnd),
    rank t E = rank t F → E = F := by
  intro t E F
  match t with
  | 0 => exact rankEarly_inj E F
  | 1 => exact rankEarly_inj E F
  | n + 2 =>
    simp only [rank]
    split
    · exact rankEven_inj E F
    · exact rankOdd_inj E F

/-- The chosen action's end always carries rank 0: the orders
    co-vary with the history. -/
theorem rank_act_end : ∀ (t : Nat) (E : CrusoeEnd),
    CrusoeEndOf (act t) E → rank t E = 0 := by
  intro t E h
  match t with
  | 0 => cases E <;> first | rfl | exact h.elim
  | 1 => cases E <;> first | rfl | exact h.elim
  | n + 2 =>
    by_cases hp : n % 2 = 0
    · simp only [act, if_pos hp] at h
      simp only [rank, if_pos hp]
      cases E <;> first | rfl | exact h.elim
    · simp only [act, if_neg hp] at h
      simp only [rank, if_neg hp]
      cases E <;> first | rfl | exact h.elim

/-- **The ℕ-time Crusoe model.**  Lean's acceptance of this
    instance block is a constructive consistency proof of the
    full base theory — (T0)–(T6), (P1)–(P6), (C1), (O0)–(O4),
    (S1) — which no finite structure can witness. -/
instance crusoeNatModel : PraxeologyFull where
  Actor := CrusoeActor
  Action := CrusoeAction
  EndE := CrusoeEnd
  Thing := CrusoeThing
  Time := Nat
  Lt := (· < ·)
  Acts := NatActs
  Avail := NatAvail
  EndOf := CrusoeEndOf
  Use := CrusoeUse
  Result := CrusoeResult
  Consumable := CrusoeConsumable
  Pref := NatPref

  -- Time order: the standard strict order on ℕ.
  T1_irrefl := fun t => Nat.lt_irrefl t
  T2_trans := fun _ _ _ h₁ h₂ => Nat.lt_trans h₁ h₂
  T3_trichot := fun t s => by omega
  T4_nontriv := ⟨0, 1, by omega⟩
  T0_first := ⟨0, fun t => by omega⟩
  T5_irrev := fun t s h h' => by omega
  T6_succ := fun t => ⟨t + 1, by omega, by rintro ⟨r, h₁, h₂⟩; omega⟩

  -- (P1) Forage is always available.
  P1 := fun _ t => ⟨forage, trivial⟩

  -- (P2) The history respects the menus.
  P2 := by
    intro a α t h
    rw [show α = act t from h]
    match t with
    | 0 => trivial
    | 1 => show 1 ≤ 1; omega
    | n + 2 =>
      by_cases hp : n % 2 = 0
      · simp only [act, if_pos hp]; show 2 ≤ n + 2; omega
      · simp only [act, if_neg hp]; show 1 ≤ n + 2; omega

  -- (P3)/(P4): same EndOf table as the finite model.
  P3 := by
    intro α
    cases α
    · exact ⟨subsist,    trivial⟩
    · exact ⟨capital,    trivial⟩
    · exact ⟨shoreCatch, trivial⟩
    · exact ⟨capital,    trivial⟩
    · exact ⟨deepCatch,  trivial⟩
  P4 := by
    intro α E F hE hF
    cases α <;> cases E <;> cases F <;>
      first | rfl | exact hE.elim | exact hF.elim

  -- (P5) The history is a function of time.
  P5 := by
    intro a α β t s hα hβ hne hts
    subst hts
    exact hne ((show α = act t from hα).trans
               (show β = act t from hβ).symm)

  -- (C1) Likewise.
  C1 := fun a t α β hα hβ =>
    (show α = act t from hα).trans (show β = act t from hβ).symm

  -- (P6) Every used thing has an idle slot — this is where the
  -- non-greedy history earns its keep (act 2 = DeepSeaFish,
  -- act 3 = ShoreFish).
  P6 := by
    intro a t α x hAct hUse
    cases a
    cases α <;> cases x <;> (try exact hUse.elim)
    · exact ⟨buildNet, 2, trivial, trivial,
             (by show buildNet ≠ act 2; decide)⟩
    · exact ⟨shoreFish, 2, (by show (1:Nat) ≤ 2; omega), trivial,
             (by show shoreFish ≠ act 2; decide)⟩
    · exact ⟨buildBoat, 2, (by show (1:Nat) ≤ 2; omega), trivial,
             (by show buildBoat ≠ act 2; decide)⟩
    · exact ⟨deepSeaFish, 3, (by show (2:Nat) ≤ 3; omega), trivial,
             (by show deepSeaFish ≠ act 3; decide)⟩
    · exact ⟨deepSeaFish, 3, (by show (2:Nat) ≤ 3; omega), trivial,
             (by show deepSeaFish ≠ act 3; decide)⟩

  -- (S1) BuildNet and BuildBoat compete for wood at t = 1.
  S1 := ⟨crusoe, 1, buildNet, buildBoat, wood,
         (by intro h; cases h), trivial,
         (by show (1:Nat) ≤ 1; omega),
         trivial, trivial⟩

  -- (O0) Grounding: the chosen end has rank 0, every other end
  -- has positive rank (by injectivity).  No availability data is
  -- needed: the orders were built to contain the record.
  O0_grounding := by
    intro a t E F hRev
    obtain ⟨hEF, α, _, hact, _, _, hαE, _⟩ := hRev
    rw [show α = act t from hact] at hαE
    show rank t E < rank t F
    have hE0 : rank t E = 0 := rank_act_end t E hαE
    have hF0 : rank t F ≠ 0 := by
      intro h0
      exact hEF (rank_inj t E F (by rw [hE0, h0]))
    omega

  -- (O1) The history acts at every moment.
  O1_always := fun _ t => ⟨act t, rfl⟩

  -- (O2) Totality from rank-injectivity and ℕ-trichotomy.
  O2_total := by
    intro a t E F hne _ _
    rcases Nat.lt_trichotomy (rank t E) (rank t F) with h | h | h
    · exact Or.inl h
    · exact absurd (rank_inj t E F h) hne
    · exact Or.inr h

  -- (O3)/(O4): the order is a strict total order at each t.
  O3_trans := fun _ _ _ _ _ h₁ h₂ => Nat.lt_trans h₁ h₂
  O4_asymm := fun _ _ _ _ h h' => absurd (Nat.lt_trans h h') (Nat.lt_irrefl _)

end NatCrusoe

/-! Sanity checks on the infinite model: at an even time the
    chosen deep-sea catch tops the scale; at an odd time the
    shore catch does — the preference reversal of `rem:constancy`,
    machine-checked. -/

example : NatCrusoe.NatPref CrusoeActor.crusoe 4
    CrusoeEnd.deepCatch CrusoeEnd.shoreCatch := by
  show NatCrusoe.rank 4 CrusoeEnd.deepCatch
     < NatCrusoe.rank 4 CrusoeEnd.shoreCatch
  decide
example : NatCrusoe.NatPref CrusoeActor.crusoe 5
    CrusoeEnd.shoreCatch CrusoeEnd.deepCatch := by
  show NatCrusoe.rank 5 CrusoeEnd.shoreCatch
     < NatCrusoe.rank 5 CrusoeEnd.deepCatch
  decide

/-- `prop:chosen_max` exercised on the infinite model: at t = 4
    (a deep-sea day) the chosen end DeepCatch outranks the
    available alternative Subsist. -/
example :
    @PraxeologyFull.Pref NatCrusoe.crusoeNatModel
      CrusoeActor.crusoe (4 : Nat) CrusoeEnd.deepCatch CrusoeEnd.subsist :=
  PraxeologyFull.chosen_end_tops_scale
    CrusoeActor.crusoe (4 : Nat) CrusoeAction.deepSeaFish
    CrusoeEnd.deepCatch CrusoeEnd.subsist
    (by show CrusoeAction.deepSeaFish = NatCrusoe.act 4; decide)
    trivial (by intro h; cases h)
    CrusoeAction.forage trivial trivial

-- Useful checks: ask Lean to print the types of our results.
#check @Praxeology.revPref_eq_of_both
#check @Praxeology.revPref_asymm
#check @Praxeology.opportunity_cost
#check @Praxeology.Order
#check @CrusoeOrder_total
#check @crusoeModel
#check @PraxeologyMU.EndAt
#check @PraxeologyMU.Serviceable
#check @PraxeologyMU.Served
#check @PraxeologyMU.ServedExcept
#check @PraxeologyMU.servedExcept_served
#check @PraxeologyMU.served_choice_relevant
#check @PraxeologyMU.DMU
#check @PraxeologyMU.DMU_structure
#check @waterFishModel
#check @PraxeologyFull
#check @PraxeologyFull.chosen_end_tops_scale
#check @NatCrusoe.crusoeNatModel

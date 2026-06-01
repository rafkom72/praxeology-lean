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
`Pref`, and the axioms (O3) `Pref_trans`, asymmetry `Pref_asymm`,
the functionality half of (MU0), and (MU4) top-segment.  Then the
diminishing-marginal-utility theorem (`thm:DMU` of the Foundations
paper §3.2, in its corrected Option-B' form with hypotheses
(i)/(ii)/(iii)) and its structure-preservation corollary
(`cor:dmu_structure`) are stated and machine-verified, mirroring
Steps 1–2 of the appendix proof `app:dmu_proof`.

Further enrichments — ownership, exchange, monetary calculation,
the transition map, and a worked Crusoe (MU)-instance with concrete
Good/UnitOf/Allot/Pref structure — are deferred to future Lean
stages, paralleling the future-research directions sketched in §5
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

/-- Following Mises, preference is **defined** in terms of choice:
    `RevPref a t E F` says actor `a` reveals a preference for end
    `E` over end `F` at time `t` because `a` chose an action whose
    end is `E` while an action whose end is `F` was simultaneously
    available. -/
def Praxeology.RevPref [P : Praxeology]
    (a : P.Actor) (t : P.Time) (E F : P.EndE) : Prop :=
  ∃ α β : P.Action,
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
  obtain ⟨α₁, _, hα₁_acts, _, _, hα₁_E, _⟩ := h₁
  obtain ⟨α₂, _, hα₂_acts, _, _, hα₂_F, _⟩ := h₂
  have heq : α₁ = α₂ := P.C1 a t α₁ α₂ hα₁_acts hα₂_acts
  rw [heq] at hα₁_E
  exact P.P4 α₂ E F hα₁_E hα₂_F

/-- **Asymmetry of revealed preference (Proposition 2.3).**
    For distinct ends, revealing `E ≻ F` rules out `F ≻ E`. -/
theorem revPref_asymm
    (a : P.Actor) (t : P.Time) (E F : P.EndE)
    (h_ne : E ≠ F) (h : RevPref a t E F) : ¬ RevPref a t F E := by
  intro h'
  exact h_ne (revPref_eq_of_both a t E F h h')

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
  ⟨buildNet, forage, trivial, trivial,
   (by intro h; cases h), trivial, trivial⟩

/-- Crusoe does NOT reveal `Subsist ≻ Capital` at t0
    (asymmetry of revealed preference applied to the model above). -/
example :
    ¬ @Praxeology.RevPref crusoeModel crusoe t0 subsist capital := by
  apply @Praxeology.revPref_asymm crusoeModel crusoe t0 capital subsist
  · intro h; cases h
  · exact ⟨buildNet, forage, trivial, trivial,
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
  ⟨buildBoat, shoreFish, trivial, trivial,
   (by intro h; cases h), trivial, trivial⟩

/-- At t2, Crusoe reveals `DeepCatch ≻ Capital`: he chose
    DeepSeaFish (consume the deep-sea catch) over BuildBoat
    (build another boat — also at end Capital). With both pieces
    of capital already in hand, realised consumption now outranks
    further deepening. -/
example :
    @Praxeology.RevPref crusoeModel crusoe t2 deepCatch capital :=
  ⟨deepSeaFish, buildBoat, trivial, trivial,
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
      * `Pref_trans`  : (O3) transitivity of preference.
      * `Pref_asymm`  : strict-order convention; together with
                        transitivity gives irreflexivity.
      * `MU0_func`    : functionality half of (MU0) ---
                        each unit allots to at most one end.
      * `MU4_top`     : (MU4) preference-respecting allocation
                        (the served set is a top-segment of
                        the choice menu under `Pref`).

    The remaining (MU)-axioms (the feasibility half of MU0,
    (MU2) menu-level fungibility, (MU3*) scarcity awareness)
    are not invoked by the theorem or its corollary and are
    omitted here.  (MU2) and (MU3*) are semantic and
    non-vacuity premises respectively; landing them in Lean is
    a routine extension. -/
class PraxeologyMU extends Praxeology where
  Good      : Type
  UnitOf    : Thing → Good → Prop
  Allot     : Actor → Time → Thing → EndE → Prop
  Pref      : Actor → Time → EndE → EndE → Prop

  Pref_trans : ∀ (a : Actor) (t : Time) (E F G : EndE),
                  Pref a t E F → Pref a t F G → Pref a t E G
  Pref_asymm : ∀ (a : Actor) (t : Time) (E F : EndE),
                  Pref a t E F → ¬ Pref a t F E

  MU0_func   : ∀ (a : Actor) (t : Time) (x : Thing) (E F : EndE),
                  Allot a t x E → Allot a t x F → E = F
  MU4_top    : ∀ (a : Actor) (t : Time) (g : Good) (E F : EndE),
                  (∃ x : Thing, UnitOf x g ∧ Allot a t x E) →
                  (∃ α : Action, Avail a α t ∧ EndOf α F) →
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

end PraxeologyMU

----------------------------------------------------------------
-- SECTION 10.  Diminishing Marginal Utility
----------------------------------------------------------------

namespace PraxeologyMU
variable [P : PraxeologyMU]

/-- **Theorem (Diminishing marginal utility)** ---
    Theorem `thm:DMU`, the corrected Option-B' statement.

    Let `y` be a unit of good `g` allotted at `(a,t)` to a
    choice-relevant end `E`.  Suppose:
      (i)   *Uniqueness on E* --- no other unit of `g` is
            allotted to `E`.
      (ii)  *Marginality of E* --- `E` is the least-preferred
            end currently served by `g` at `(a,t)`.
      (iii) *Reduced marginal E** --- the reduced served set
            `ServedExcept a t g y` has a least-preferred
            element `E*`.
    Then `E* ≻ E`.

    The proof matches Steps 1–2 of the appendix proof
    `app:dmu_proof` verbatim.  It uses only the
    hypotheses --- no (MU)-axiom is invoked, because the
    structural content is concentrated in (ii). -/
theorem DMU
    (a : P.Actor) (t : P.Time) (g : P.Good)
    (y : P.Thing) (E E_star : P.EndE)
    -- Setup of the theorem statement
    (_hyUnit : P.UnitOf y g)
    (_hyAllot : P.Allot a t y E)
    (_hyEndAt : EndAt a t E)
    -- (i) Uniqueness on E
    (uniq : ∀ x : P.Thing,
              P.UnitOf x g → P.Allot a t x E → x = y)
    -- (ii) Marginality of E in the full state
    (marg : ∀ F : P.EndE,
              Served a t g F → P.Pref a t F E ∨ F = E)
    -- (iii) E_star exists in the reduced state
    (e_redServed : ServedExcept a t g y E_star)
    (_e_redMarg  : ∀ F : P.EndE,
                     ServedExcept a t g y F →
                     P.Pref a t F E_star ∨ F = E_star)
    : P.Pref a t E_star E := by
  -- Unpack e_redServed: x ≠ y allotted to E_star.
  obtain ⟨x, hxUnit, hxNe, hxAllot⟩ := e_redServed
  -- Drop the `x ≠ y` constraint to recover Served E_star.
  have hServed : Served a t g E_star := ⟨x, hxUnit, hxAllot⟩
  -- Apply marginality (ii) to E_star.
  rcases marg E_star hServed with hpref | heq
  ·  -- Case Pref E_star E: done.
    exact hpref
  ·  -- Case E_star = E: contradiction with (i).
    rw [heq] at hxAllot
    exact absurd (uniq x hxUnit hxAllot) hxNe

/-- **Corollary (Structure preservation under marginal removal)**
    --- Corollary `cor:dmu_structure`.

    Under the hypotheses of `DMU`, the reduced served set
    `ServedExcept a t g y` is itself a top-segment of the
    choice menu under `Pref`, i.e. (MU4) continues to hold
    for the "y-removed" allotment.

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
        P.Pref a t G F' →
        ServedExcept a t g y G := by
  intro F' G hF' hG hpref
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
  -- (MU4)-top-segment: G ≻ F' and F' served implies G served.
  have hGServed : Served a t g G :=
    P.MU4_top a t g F' G hF'Served hG hpref
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
#check @PraxeologyMU.DMU
#check @PraxeologyMU.DMU_structure

-- A Mealy machine is a 6-tuple ( S , S 0 , Σ , Λ , T , G ) {\displaystyle (S,S_{0},\Sigma ,\Lambda ,T,G)} consisting of the following:

--     a finite set of states S {\displaystyle S}
--     a start state (also called initial state) S 0 {\displaystyle S_{0}} which is an element of S {\displaystyle S}
--     a finite set called the input alphabet Σ {\displaystyle \Sigma }
--     a finite set called the output alphabet Λ {\displaystyle \Lambda }
--     a transition function T : S × Σ → S {\displaystyle T:S\times \Sigma \rightarrow S} mapping pairs of a state and an input symbol to the corresponding next state.
--     an output function G : S × Σ → Λ {\displaystyle G:S\times \Sigma \rightarrow \Lambda } mapping pairs of a state and an input symbol to the corresponding output symbol.

-- In some formulations, the transition and output functions are coalesced into a single function T : S × Σ → S × Λ {\displaystyle T:S\times \Sigma \rightarrow S\times \Lambda }.

-- A Moore machine is the same, except the output function can only depend on the state, and not the input

-- We prove that the Moore and Mealey formalisms are equivalent.

inductive StateMachineType
  -- [tag:state_machine_type_cases_order]
  | Moore
  | Mealey

-- [tag:in_the_type_or_in_the_value]
-- In this formulation, the machine "type" is encoded in the type type.
-- An alternative formulation would just have a sum type over possible output types
-- but then you would carry a proof, too.
-- This is a design question about intrinsic versus extrinsic properties...
-- https://goosetaco.notion.site/Put-it-in-the-type-or-in-the-value-2d6b480b02ca44f79dffb8760a9ee8c8

structure StateMachine
  (machine_type : StateMachineType)
  (input_space : Type)
  (output_space : Type)
where
  state_space : Type
  s0 : state_space
  transition : state_space -> input_space -> state_space
  output : match machine_type with
  -- surprisingly, this has to match the order too?
  -- [ref:state_machine_convoy_pattern]
  -- [ref:state_machine_type_cases_order]
  | .Moore => state_space -> output_space
  | .Mealey => state_space -> input_space -> output_space

-- This is a machine that outputs the count, mod 3, of how many times a `one` came in
def counter_mod_3 :
  StateMachine
    .Mealey
    (input_space := Fin 2)
    (output_space := Fin 3)
:= {
  state_space := Fin 3,
  s0 := 0,

  -- if you match instead on `x, y`, you get an error about missing cases
  transition := fun s i =>
    match i, s with
    | 0, _ => s
    | 1, 0 => 1
    | 1, 1 => 2
    | 1, 2 => 0
  output := fun s _ => s
}

def moore_to_mealey (i o: Type) (moore : StateMachine .Moore i o ) : StateMachine .Mealey i o
:= {
  state_space := moore.state_space,
  s0 := moore.s0,
  transition := moore.transition
  output := fun s _ => moore.output s
}

-- just debugging stuff
#check StateMachineType.casesOn
#check StateMachineType.recOn

def transduce_helper
  (mt : StateMachineType)
  (i o : Type)
  (machine : StateMachine mt i o) -- this carries s0, but we do not need it
  (current_state : machine.state_space)
  (input : List i)
  :=
  match input with
  | List.nil => List.nil
  | List.cons y ys =>
    let next_state := machine.transition current_state y
    let s := machine.state_space
    -- [tag:state_machine_convoy_pattern]
    -- [ref:in_the_type_or_in_the_value]
    let a_motive (mt2 : StateMachineType) :=
      let machine_dot_output_type := match mt2 with
      -- s->o and s->i->o are the types of machine.output
      | .Moore => (s -> o)
      | .Mealey => (s -> i -> o)

      machine_dot_output_type -> o

    let make_next_output :=
    (
      StateMachineType.casesOn
      (
        motive := a_motive
      )
      mt
      -- [ref:state_machine_type_cases_order]
      (fun f => f next_state)
      (fun f => f next_state y)
    )

    let next_output := make_next_output machine.output
    (List.cons next_output (transduce_helper mt i o machine next_state ys))

def transduce (mt : StateMachineType) (i o : Type) machine ys :=
  transduce_helper mt i o machine machine.s0 ys

namespace test
def input : List (Fin 2) := [0, 1, 1, 0, 1, 1]
def output := transduce _ _ _ counter_mod_3 input
#reduce output.map (fun n => n.val)
end test

-- This is my first time seeing a dependent fold, where the "accumulator" changes type
-- (Yes, I have an imperative for-loop-y brain)
-- Some notes
-- fold : (motive : Type) -> (T : Type) -> List T -> (init : motive) -> (motive -> T -> motive) -> motive

-- fold :
-- (motive : List T -> Type)
-- -> (T : Type)
-- -> (a : List T)
-- -> (init : motive [])
-- -> ((tail : List T) -> motive tail -> (head: T) -> motive (cons head tail))
-- -> motive a

theorem moore_to_mealey_same_state_space
  (i o: Type) (moore : StateMachine .Moore i o ) :
  moore.state_space = (moore_to_mealey _ _ moore).state_space :=
  Eq.refl _

theorem moore_to_mealey_same_io_behavior
  (i o: Type) (moore : StateMachine .Moore i o ) (is : List i):
  let mealey := (moore_to_mealey _ _ moore)
  transduce _ _ _ moore is = transduce _ _ _ mealey is
:= by
  unfold transduce moore_to_mealey
  simp
  generalize H : moore.s0 = s
  rewrite (config := {occs := .pos [2]}) [← H]
  clear H
  revert s
  induction is with
  | nil =>
      intro s
      rfl
  | cons head tail tail_ih =>
      intro s
      unfold transduce_helper
      simp
      rw [tail_ih]

-- This is a construction where the state is augmented with the output
structure MooreStateFromMealeyO (state_space output_space: Type)
where
  s : state_space
  o : output_space

def mealey_to_moore_o (i o: Type) (o1 : o) (mealey : StateMachine .Mealey i o ) : StateMachine .Moore i o
:= {
  state_space := MooreStateFromMealeyO mealey.state_space o,
  s0 := {s := mealey.s0, o := o1},
  transition := fun s i =>
    let s' := mealey.transition s.s i
    {s := s', o := mealey.output s' i}
  output := fun s => s.o
}

-- This is a construction where the state is augmented with the input
structure MooreStateFromMealeyI (state_space input_space: Type)
where
  s : state_space
  i : input_space

def mealey_to_moore_i (i o: Type) (i1 : i) (mealey : StateMachine .Mealey i o ) : StateMachine .Moore i o
:= {
  state_space := MooreStateFromMealeyI mealey.state_space i,
  s0 := {s := mealey.s0, i := i1},
  transition := fun s i =>
    let s' := mealey.transition s.s i
    {s := s', i := i}
  output := fun s => mealey.output s.s s.i
}

namespace test2
def mealey := counter_mod_3
def input : List (Fin 2) := [0, 1, 1, 0, 1, 1]
def output_mealey := transduce _ _ _ mealey input
def arb_i : (Fin 2) := 1
def arb_o : (Fin 3) := 1
def moore_i := mealey_to_moore_i _ _ arb_i mealey
def moore_o := mealey_to_moore_o _ _ arb_o mealey

def output_moore_i := transduce _ _ _ moore_i input
def output_moore_o := transduce _ _ _ moore_o input

-- all of these are the same
#reduce output_mealey
#reduce output_moore_i
#reduce output_moore_o
end test2


theorem mealey_to_moore_o_same_io_behavior
  (i o: Type) (mealey : StateMachine .Mealey i o) (is : List i) (o1 : o):
  let moore := (mealey_to_moore_o _ _ o1 mealey)
  transduce _ _ _ mealey is = transduce _ _ _ moore is
:= by
  unfold transduce
  unfold mealey_to_moore_o
  simp -- get rid of let
  generalize H : mealey.s0 = s
  rewrite (config := {occs := .pos [2]}) [← H]
  clear H
  generalize H2 : o1 = o2
  rewrite (config := {occs := .pos [1]}) [← H2]
  clear H2
  revert s o2
  induction is with
  | nil =>
      intro s o1
      rfl
  | cons head tail tail_ih =>
      intro s o1
      unfold transduce_helper
      simp
      rw [tail_ih _ (mealey.output (mealey.transition s head) head)]

theorem mealey_to_moore_i_same_io_behavior
  (i o: Type) (mealey : StateMachine .Mealey i o) (is : List i) (i1 : i):
  let moore := (mealey_to_moore_i _ _ i1 mealey)
  transduce _ _ _ mealey is = transduce _ _ _ moore is
:= by
  unfold transduce
  unfold mealey_to_moore_i
  simp -- get rid of let
  generalize H : mealey.s0 = s
  rewrite (config := {occs := .pos [2]}) [← H]
  clear H
  generalize H2 : i1 = i2
  rewrite (config := {occs := .pos [1]}) [← H2]
  clear H2
  revert s i2
  induction is with
  | nil =>
      intro s o1
      rfl
  | cons head tail tail_ih =>
      intro s o1
      unfold transduce_helper
      simp
      -- https://chatgpt.com/share/67c9d856-5aec-800a-8646-5ebb8d0e5497
      rw [tail_ih _ head]

(* Coq 8.5pl5 with ssreflect 1.5. *)
(* On ProofGeneral 4.3pre150930.  *)


Require Import String.
Require Import List.
Require Import FMapInterface.

Require Import ssreflect ssrbool.

Module Lang.

  (* TODO: sort by opcode *)
  Inductive instr := (** partial.  adding those necessary. *)
  | STOP
  | ADD
  | MUL
  | SUB
  | DIV
  | EXP
  | instr_GT
  | instr_EQ
  | AND
  | ISZERO
  | CALLER
  | GAS
  | CALLVALUE
  | CALLDATALOAD
  | CALLDATASIZE
  | CALLDATACOPY
  | TIMESTAMP
  | POP
  | MLOAD
  | MSTORE
  | SLOAD
  | SSTORE
  | JUMP
  | JUMPI
  | JUMPDEST
  | PUSH_N : string -> instr
  | DUP1
  | DUP2
  | DUP3
  | DUP4
  | DUP5
  | DUP6
  | DUP7
  | DUP8
  | DUP9
  | SWAP1
  | SWAP2
  | SWAP3
  | SWAP4
  | CALL
  | LOG2
  | LOG3
  | RETURN
  | SUICIDE
  .

  Fixpoint string_half_len str :=
    match str with
    | String _ (String _ tl) => S (string_half_len tl)
    | _ => O
    end.

  Definition instr_length (i : instr) : nat :=
    match i with
    | PUSH_N str => string_half_len str
    | _ => 1
    end.

  Fixpoint drop_bytes (prog : list instr) (bytes : nat) {struct bytes} :=
    match prog, bytes with
    | _, O => prog
    | PUSH_N str :: tl, S pre =>
      drop_bytes tl (pre - (string_half_len str - 1))
    | _ :: tl, S pre =>
      drop_bytes tl pre
    | nil, S _ => nil
    end.

  Definition example2 :=
  (* taken from
     https://etherchain.org/account/0xad8d3a5d2d92eb14bb56ca9f380be35b8efe0c04#codeDisasm *)
    PUSH_N "0x60" ::
    PUSH_N "0x40" ::
    MSTORE ::
    CALLDATASIZE ::
    ISZERO ::
    PUSH_N "0x0053" ::
    JUMPI ::
    PUSH_N "0x00" ::
    CALLDATALOAD ::
    PUSH_N "0x0100000000000000000000000000000000000000000000000000000000" ::
    SWAP1 ::
    DIV ::
    DUP1 ::
    PUSH_N "0x3feb1bd8" ::
    instr_EQ ::
    PUSH_N "0x00aa" ::
    JUMPI ::
    DUP1 ::
    PUSH_N "0x6042a760" ::
    instr_EQ ::
    PUSH_N "0x00c9" ::
    JUMPI ::
    DUP1 ::
    PUSH_N "0xb214faa5" ::
    instr_EQ ::
    PUSH_N "0x00ee" ::
    JUMPI ::
    PUSH_N "0x0053" ::
    JUMP ::
    JUMPDEST ::
    PUSH_N "0x00a8" ::
    JUMPDEST ::
    CALLER ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0xceaafb6781e240ba6b317a906047690d1c227df2d967ff3f53b44f14a62c2cab" ::
    CALLVALUE ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP3 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    SWAP2 ::
    POP ::
    POP ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    SWAP2 ::
    SUB ::
    SWAP1 ::
    LOG2 ::
    JUMPDEST ::
    JUMP ::
    JUMPDEST ::
    STOP ::
    JUMPDEST ::
    PUSH_N "0x00c7" ::
    PUSH_N "0x04" ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    POP ::
    PUSH_N "0x0154" ::
    JUMP ::
    JUMPDEST ::
    STOP ::
    JUMPDEST ::
    PUSH_N "0x00ec" ::
    PUSH_N "0x04" ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    POP ::
    PUSH_N "0x0233" ::
    JUMP ::
    JUMPDEST ::
    STOP ::
    JUMPDEST ::
    PUSH_N "0x00ff" ::
    PUSH_N "0x04" ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    POP ::
    PUSH_N "0x0101" ::
    JUMP ::
    JUMPDEST ::
    STOP ::
    JUMPDEST ::
    DUP1 ::
    CALLER ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0x19dacbf83c5de6658e14cbf7bcae5c15eca2eedecf1c66fbca928e4d351bea0f" ::
    CALLVALUE ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP3 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    SWAP2 ::
    POP ::
    POP ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    SWAP2 ::
    SUB ::
    SWAP1 ::
    LOG3 ::
    JUMPDEST ::
    POP ::
    JUMP ::
    JUMPDEST ::
    PUSH_N "0x00" ::
    PUSH_N "0x00" ::
    SWAP1 ::
    SLOAD ::
    SWAP1 ::
    PUSH_N "0x0100" ::
    EXP ::
    SWAP1 ::
    DIV ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    CALLER ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    instr_EQ ::
    ISZERO ::
    PUSH_N "0x022d" ::
    JUMPI ::
    DUP2 ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0x00" ::
    DUP3 ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    SWAP1 ::
    POP ::
    PUSH_N "0x00" ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP4 ::
    SUB ::
    DUP2 ::
    DUP6 ::
    DUP9 ::
    DUP9 ::
    CALL ::
    SWAP4 ::
    POP ::
    POP ::
    POP ::
    POP ::
    POP ::
    DUP2 ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    DUP4 ::
    PUSH_N "0x4c13017ee95afc4bbd8a701dd9fbc9733f1f09f5a1b5438b5b9abd48e4c92d78" ::
    DUP4 ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP3 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    SWAP2 ::
    POP ::
    POP ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    SWAP2 ::
    SUB ::
    SWAP1 ::
    LOG3 ::
    JUMPDEST ::
    JUMPDEST ::
    POP ::
    POP ::
    POP ::
    JUMP ::
    JUMPDEST ::
    PUSH_N "0x00" ::
    PUSH_N "0x00" ::
    SWAP1 ::
    SLOAD ::
    SWAP1 ::
    PUSH_N "0x0100" ::
    EXP ::
    SWAP1 ::
    DIV ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    CALLER ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    instr_EQ ::
    ISZERO ::
    PUSH_N "0x034b" ::
    JUMPI ::
    DUP3 ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0xb214faa5" ::
    DUP3 ::
    DUP5 ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP4 ::
    PUSH_N "0x0100000000000000000000000000000000000000000000000000000000" ::
    MUL ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x04" ::
    ADD ::
    DUP1 ::
    DUP3 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    SWAP2 ::
    POP ::
    POP ::
    PUSH_N "0x00" ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP4 ::
    SUB ::
    DUP2 ::
    DUP6 ::
    DUP9 ::
    PUSH_N "0x8502" ::
    GAS ::
    SUB ::
    CALL ::
    ISZERO ::
    PUSH_N "0x0002" ::
    JUMPI ::
    POP ::
    POP ::
    POP ::
    POP ::
    DUP3 ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    DUP5 ::
    PUSH_N "0x260c3af1b30cb645202dd6dbf41affda680b1ffebd32d401b7f121c2b9262680" ::
    DUP5 ::
    DUP5 ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP4 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    DUP3 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    SWAP3 ::
    POP ::
    POP ::
    POP ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    SWAP2 ::
    SUB ::
    SWAP1 ::
    LOG3 ::
    JUMPDEST ::
    JUMPDEST ::
    POP ::
    POP ::
    POP ::
    POP ::
    JUMP :: nil.

End Lang.

Module EVM (U256:OrderedType).

  Import Lang.

  Parameter is_zero : U256.t -> bool.
  Parameter zero : U256.t.
  Parameter one  : U256.t.
  Parameter succ : U256.t -> U256.t.
  Parameter to_nat : U256.t -> nat.
  Parameter sub : U256.t -> U256.t -> U256.t.
  Parameter add : U256.t -> U256.t -> U256.t.
  Parameter and : U256.t -> U256.t -> U256.t.

  Definition stack := list U256.t.

  Require Import FMapList.

  Module Memory := Make (U256).

  Definition memory := Memory.t U256.t.

  Definition m T := option (T * memory).

  Definition operation := stack -> memory -> m stack (* maybe with side-effect? *).

  (* trying to encode
     https://etherchain.org/account/0x10ebb6b1607de9c08c61c6f6044b8edc93b8e9c9#codeDisasm
  *)

  Require Import List.

  Definition push_x (d : U256.t) : operation :=
    fun s mem => Some (d :: s, mem).

  Definition pop : operation :=
    fun s mem =>
      match s with
        | nil => None
        | hd :: tl => Some (tl, mem)
      end.

  Definition mstore : operation :=
    fun s mem =>
      match s with
        | nil => None
        | _ :: nil => None
        | a :: b :: l => Some (l, Memory.add a b (* not precise, has to be devided into 32 *) mem)
      end.

  Definition mload : operation :=
    fun s mem =>
      match s with
        | nil => None
        | addr :: l =>
          Some (match Memory.find addr mem with Some b => b | None => zero end :: l, mem)
      end.


  Definition gas remaining_gas : operation :=
    fun s mem => Some (remaining_gas :: s, mem).

  Definition calldatasize size : operation :=
    fun s mem => Some (size :: s, mem).

  Definition callvalue value : operation :=
    fun s mem => Some (value :: s, mem).

  Fixpoint memwrite_n (start_addr : U256.t) (len : nat) (source : list U256.t) (mem : memory) :=
    match len with
      | O => mem
      | S len' =>
        memwrite_n (succ start_addr (* what happens when this overflows? *) ) len'
        (match source with nil => nil | _ :: tl => tl end)
        (Memory.add start_addr (match source with nil => zero | hd :: _ => hd end) mem)
    end.

  Fixpoint drop {A : Type} (n : nat) (lst : list A) :=
    match n, lst with
      | O, _ => lst
      | _, nil => nil
      | S pre, _ :: tl => drop pre tl
    end.

  Definition calldatacopy (input : list U256.t) : operation :=
    fun s mem =>
      match s with
        | m0 :: m1 :: m2 :: l =>
          Some (l, memwrite_n m0 (to_nat m2) (drop (to_nat m1) input) mem)
        | _ => None
      end.

  Definition iszero : operation :=
    fun s mem =>
      match s with
        | nil => None
        | h :: tl =>
          Some ((if is_zero h then one else zero) :: tl, mem)
      end.

  Definition two_two_op (f : U256.t -> U256.t -> (U256.t * U256.t)) : operation :=
    fun s mem =>
      match s with
        | a :: b :: l =>
          Some (fst (f a b) :: snd (f a b) :: l, mem)
        | _ => None
      end.

  Parameter exp : U256.t -> U256.t -> U256.t.

  Definition two_one_op (f : U256.t -> U256.t -> U256.t) : operation :=
    fun s mem =>
      match s with
        | nil => None
        | _ :: nil => None
        | a :: b :: l => Some ((f a b) :: l, mem)
      end.

  Definition exp_op : operation := two_one_op exp.

  Definition and_op : operation := two_one_op and.

  Definition one_one_op (f : U256.t -> U256.t) : operation :=
    fun s mem =>
      match s with
        | nil => None
        | a :: l => Some (f a :: l, mem)
      end.

  Definition sload storage : operation :=
    one_one_op (fun addr => match Memory.find addr storage with Some b => b | None => zero end).

  Definition calldataload (input : list U256.t) : operation :=
    one_one_op (fun n => List.nth (to_nat n) input zero).

  Parameter div : U256.t -> U256.t -> U256.t.
  Parameter mul : U256.t -> U256.t -> U256.t.

  Definition div_op := two_one_op div.
  Definition mul_op := two_one_op mul.
  Definition add_op := two_one_op add.

  Definition dup1 : operation :=
    fun s mem =>
      match s with
        | a :: l => Some (a :: a :: l, mem)
        | _ => None (* really? *)
      end.

  Definition dup2 : operation :=
    fun s mem =>
      match s with
        | a :: b :: l => Some (b :: a :: b :: l, mem)
        | _ => None
      end.

  Definition dup3 : operation :=
    fun s mem =>
      match s with
        | a :: b :: c :: l => Some (c :: a :: b :: c :: l, mem)
        | _ => None
      end.

  Definition dup4 : operation :=
    fun s mem =>
      match s with
        | a :: b :: c :: d :: l => Some (d :: a :: b :: c :: d :: l, mem)
        | _ => None
      end.

  Fixpoint nth_opt {A} (n : nat) (lst : list A) :=
    match n, lst with
    | O, hd :: _ => Some hd
    | S pre, _ :: tl => nth_opt pre tl
    | _, _ => None
    end.

  Definition stack_dup n (s : stack) :=
    match nth_opt n s with
    | Some elm => Some (elm :: s)
    | None => None
    end.


  Definition dup_n (n : nat) : operation :=
    fun s mem =>
      match stack_dup n s with
      | Some new_s => Some (new_s, mem)
      | None => None
      end.

  Definition eq_op : operation := two_one_op
    (fun a b => match U256.compare a b with
                | EQ _ => one
                | _ => zero
              end).

  Definition gt : operation := two_one_op
    (fun a b => match U256.compare a b with
                | GT _ => one
                | _ => zero
              end).

  Definition sub_op : operation := two_one_op sub.

  Definition swap1 : operation := two_two_op (fun a b => (b, a)).

  Definition swap2 : operation :=
    fun s mem =>
      match s with
        | a :: b :: c :: l =>
          Some (c :: b :: a :: l, mem)
        | _ => None
      end.

  Definition swap3 : operation :=
    fun s mem =>
      match s with
        | a :: b :: c :: d :: l =>
          Some (d :: b :: c :: a :: l, mem)
        | _ => None
      end.

  Definition swap4 : operation :=
    fun s mem =>
      match s with
        | a :: b :: c :: d :: e :: l =>
          Some (e :: b :: c :: d :: a :: l, mem)
        | _ => None
      end.

  Parameter source_of_whatever : Set.
  Parameter read_whatever : source_of_whatever -> U256.t.
  Parameter wa : source_of_whatever -> source_of_whatever.
  Parameter initial_noise : source_of_whatever.

  Record state :=
    {   stc     : stack
      ; mem     : memory
      ; str     : memory
      ; prg_sfx : list instr
      ; program : list instr
      ; caller  : U256.t
      ; value   : U256.t
      ; data    : list U256.t
      ; time    : U256.t
      ; noise   : source_of_whatever
    }.

  Inductive result :=
  | continue : state -> result
  | suicide  : U256.t (* who gets the balance *) -> result
  | returned : state -> result
  | stopped  : state -> result
  | end_of_program : state -> result (* what actually happens? *)
  | failure :  state -> result (* what actually happens? *)
  | not_implemented : state -> result
  .

  Definition operation_sem (op : operation) (pre: state) : result :=
    match pre.(prg_sfx) with
      | nil => end_of_program pre
      | _ :: tl =>
        match op pre.(stc) pre.(mem) with
          | None => failure pre
          | Some (s,m) =>
            continue {| stc := s ;
              mem := m ;
              str := pre.(str) ;
              program := pre.(program);
              prg_sfx := tl;
              caller := pre.(caller);
              value := pre.(value);
              data  := pre.(data);
              time  := pre.(time);
              noise := pre.(noise)
            |}
        end
    end.

  Definition noop (pre : state) : result :=
    match pre.(prg_sfx) with
    | nil => end_of_program pre
    | _ :: tl =>
      continue {| stc := pre.(stc);
                  mem := pre.(mem);
                  str := pre.(str);
                  program := pre.(program);
                  prg_sfx := tl;
                  caller := pre.(caller);
                  value := pre.(value);
                  data := pre.(data);
                  time := pre.(time);
                  noise := pre.(noise)
               |}
    end.

  Definition reader (f : state -> U256.t) (pre : state) : result :=
    match pre.(prg_sfx) with
      | nil => end_of_program pre
      | _ :: tl =>
        continue {| stc := f pre :: pre.(stc) ;
          mem := pre.(mem) ;
          str := pre.(str) ;
          program := pre.(program);
          prg_sfx := tl;
          caller := pre.(caller);
          value  := pre.(value);
          data   := pre.(data);
          time   := pre.(time);
          noise  := pre.(noise)
        |}
    end.

  Definition random_reader (pre : state) : result :=
    match pre.(prg_sfx) with
      | nil => end_of_program pre
      | _ :: tl =>
        continue {| stc := read_whatever pre.(noise) :: pre.(stc) ;
                    mem := pre.(mem);
                    str := pre.(str);
                    program := pre.(program);
                    prg_sfx := tl;
                    caller := pre.(caller);
                    value := pre.(value);
                    data := pre.(data);
                    time := pre.(time);
                    noise := wa pre.(noise) |}
    end.

  Parameter U : string -> U256.t.
  Parameter Ulen : forall {a : Type}, list a -> U256.t.

  Definition instr_sem (i : instr) : state -> result :=
    match i with
      | STOP => (fun pre => stopped pre)
      | ADD => operation_sem add_op
      | MUL => operation_sem mul_op
      | SUB => operation_sem sub_op
      | DIV => operation_sem div_op
      | EXP => operation_sem exp_op
      | instr_GT  => operation_sem gt
      | instr_EQ => operation_sem eq_op
      | AND => operation_sem and_op
      | ISZERO => operation_sem iszero
      | GAS    => random_reader (* TODO: implement gas mechanism somehow *)
      | CALLER => reader caller
      | CALLVALUE => reader value
      | CALLDATALOAD => (fun pre => operation_sem (calldataload pre.(data)) pre)
      | CALLDATASIZE => reader (fun st => Ulen (st.(data)))
      | CALLDATACOPY => (fun pre => operation_sem (calldatacopy pre.(data)) pre)
      | TIMESTAMP => reader time
      | POP =>    operation_sem pop
      | MLOAD  => operation_sem mload
      | MSTORE => operation_sem mstore
      | SLOAD => (fun pre => operation_sem (sload pre.(str)) pre)
      | SSTORE => (fun pre =>
                     match pre.(stc) with
                     | nil => failure pre
                     | _ :: nil => failure pre
                     | addr :: val :: stl =>
                       match pre.(prg_sfx) with
                       | nil => failure pre
                       | _ :: cont => 
                         continue {|
                             stc := stl;
                             mem := pre.(mem);
                             str := Memory.add addr val pre.(str);
                             program := pre.(program);
                             prg_sfx := cont;
                             caller := pre.(caller);
                             value := pre.(value);
                             data := pre.(data);
                             time := pre.(time);
                             noise := pre.(noise)
                           |}
                       end
                     end)
      | JUMP => (fun pre =>
                   match pre.(stc) with
                   | nil => failure pre
                   | hd :: tl =>
                     continue {|
                       stc := tl;
                       mem := pre.(mem);
                       str := pre.(str);
                       program := pre.(program);
                       prg_sfx := drop_bytes pre.(program) (to_nat hd);
                       caller := pre.(caller);
                       value := pre.(value);
                       data := pre.(data);
                       time := pre.(time);
                       noise := pre.(noise)
                     |}
                   end
                )
      | JUMPI => (fun pre =>
                    match pre.(stc) with
                    | nil => failure pre
                    | hd::nil => failure pre
                    | dst :: cond :: tl_stc =>
                      if is_zero cond then
                        match pre.(prg_sfx) with
                        | nil => failure pre
                        | _ :: tl =>
                          continue {|
                              stc := tl_stc;
                              mem := pre.(mem);
                              str := pre.(str);
                              program := pre.(program);
                              prg_sfx := tl;
                              caller := pre.(caller);
                              value := pre.(value);
                              data := pre.(data);
                              time := pre.(time);
                              noise := pre.(noise)
                            |}
                        end
                      else
                        continue {|
                            stc := tl_stc;
                            mem := pre.(mem);
                            str := pre.(str);
                            program := pre.(program);
                            prg_sfx := drop_bytes pre.(program) (to_nat dst);
                            caller := pre.(caller);
                            value := pre.(value);
                            data := pre.(data);
                            time := pre.(time);
                            noise := pre.(noise)
                          |}
                    end)
      | JUMPDEST =>
        (fun pre => match pre.(prg_sfx) with
                      | nil => failure pre
                      | _ :: tl =>
                        continue {|
                            stc := pre.(stc);
                            mem := pre.(mem);
                            str := pre.(str);
                            program := pre.(program);
                            prg_sfx := tl;
                            caller := pre.(caller);
                            value := pre.(value);
                            data := pre.(data);
                            time := pre.(time);
                            noise := pre.(noise)
                            |}
                    end)
      | PUSH_N str => operation_sem (push_x (U str))
      | DUP1 => operation_sem dup1
      | DUP2 => operation_sem dup2
      | DUP3 => operation_sem dup3
      | DUP4 => operation_sem dup4
      | DUP5 => operation_sem (dup_n 5)
      | DUP6 => operation_sem (dup_n 6)
      | DUP7 => operation_sem (dup_n 7)
      | DUP8 => operation_sem (dup_n 8)
      | DUP9 => operation_sem (dup_n 9)
      | SWAP1 => operation_sem swap1
      | SWAP2 => operation_sem swap2
      | SWAP3 => operation_sem swap3
      | SWAP4 => operation_sem swap4
      | LOG2  => noop
      | LOG3 => noop
      | CALL => not_implemented
      | RETURN => returned
      | SUICIDE => (fun pre =>
                      match pre.(stc) with
                        | nil => failure pre
                        | hd :: _ => suicide hd
                      end
                   )
    end.

  Fixpoint apply_n (n : nat) (pre : state) : result :=
    match n, pre.(prg_sfx) with
      | O, _ => continue pre
      | S n', hd::_ =>
        match instr_sem hd pre with
          | continue post =>  apply_n n' post
          | x => x
        end
      | S n', nil => end_of_program pre
    end.

  Lemma apply_S : forall n' pre,
    apply_n (S n') pre =
    match pre.(prg_sfx) with
      | hd :: _ => 
        match instr_sem hd pre with
          | continue post =>  apply_n n' post
          | x => x
        end
      | nil => end_of_program pre
    end.
  Proof.
  auto.
  Qed.


  Parameter c : U256.t.
  Parameter v : U256.t.
  Parameter d : list U256.t.
  Parameter current_time : U256.t.
  Parameter s : Memory.t U256.t.

  (* This results in a normal return. *)
  (* Maybe the execution can start in the middle.  How? *)
  Definition ex := {|
    stc := nil;
    mem := Memory.empty U256.t;
    str := s;
    program := example2;
    prg_sfx := example2;
    caller := c;
    value := v;
    data := d;
    time := current_time;
    noise := initial_noise
  |}.


  Parameter tn : (to_nat (U "0x004f")) = 79.
  Parameter hg : (to_nat (U "0x00a4")) = 164.
  Parameter gg : (to_nat (U "0x005a")) = 90.
  Lemma ff_ : U256.eq (U "0x40") (U "0x40").
  Proof. auto.  Qed.
  Parameter ff : U256.compare (U "0x40") (U "0x40") = @EQ U256.t U256.lt U256.eq (U "0x40") (U "0x40") ff_.

  Parameter zz : is_zero zero.

  Parameter somebody : U256.t.

  Definition interesting (r : result) (target : U256.t) :=
    match r with
      | continue _ => False
      | suicide _  => True
      | returned st
      | stopped st  =>
        s <> st.(str) /\ Memory.find zero st.(str) = Some target
      | failure _ => True
      | end_of_program _ => True
      | not_implemented _ => True
    end.

  Ltac run :=
    repeat (rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting find Memory.find Memory.add]).

  Goal interesting (apply_n 1000 ex) somebody -> False.
    run.
    set b0 := is_zero _.
    case_eq b0 => b0_eq.
    {
      run.
      set b1 := is_zero _.
      case_eq b1 => b1_eq.
      {
        run.
        set b2 := is_zero _.
        case_eq b2 => b2_eq.
        {
          run.
          set b3 := is_zero _.
          case_eq b3 => b3_eq.
          {
            run.
            have -> : (to_nat (U "0x0053")) = 83 by admit.
            compute [drop_bytes string_half_len minus].
            run.


            Lemma find_add :
              forall k (v : U256.t) orig,
                Memory.find k (Memory.add k v orig) = Some v.
            Proof.
            Admitted.

            rewrite find_add.

            set found := Memory.find _ _.
            have -> : found = Some (U "0x60") by admit.

            have -> : (to_nat (U "0x60")) = 96 by admit.
            compute [drop_bytes string_half_len minus].

            run.

            set dst := to_nat _.

            have -> : dst = 96 by admit.




  Ltac run2 :=
    repeat (rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting find Memory.find Memory.add]).




            rewrite ff.
            rewrite-/find.
            set x := _ (U "0x40") _.
            have -> : x = Some (U "0x60") by admit.
            have -> : (to_nat (U "0x60")) = 96 by admit.
            compute [drop_bytes string_half_len minus].
            run.

          }
          {}
        }
        {
        }
      }
      {}
    }
    {
    }

End EVM.

Require Import FMapInterface.
Require Import String.
Require Import List.

Module Lang.

  Inductive instr := (** partial.  adding as necessary. *)
  | STOP
  | ADD
  | SUB
  | DIV
  | EXP
  | GT
  | instr_EQ
  | AND
  | ISZERO
  | CALLER
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
  | SWAP1
  | SWAP2
  | RETURN
  | SUICIDE
  .

  Definition example1_part1 : list instr :=
    ( PUSH_N "0x60" ::
      PUSH_N "0x40" ::
      MSTORE ::
      PUSH_N "0x00" ::
      CALLDATALOAD ::
      PUSH_N "0x0100000000000000000000000000000000000000000000000000000000" ::
      SWAP1 ::
      DIV ::
      DUP1 ::
      PUSH_N "0x4665096d" :: nil).

  Definition example1_part2 : list instr :=
      instr_EQ ::
      PUSH_N "0x004f" ::
      JUMP ::
      DUP1 ::
      PUSH_N "0xbe040fb0" ::
      instr_EQ ::
      PUSH_N "0x0070" ::
      JUMPI ::
      DUP1 ::
      PUSH_N "0xdd467064" ::
      instr_EQ ::
      PUSH_N "0x007d" ::
      JUMPI ::
      PUSH_N "0x004d" ::
      JUMP ::
      JUMPDEST ::
      STOP ::
      JUMPDEST ::
      PUSH_N "0x005a" ::
      PUSH_N "0x04" :: nil.

  Definition example1_part3 :=
      POP ::
      PUSH_N "0x00a4" ::
      JUMP ::
      JUMPDEST ::
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
      RETURN ::
      JUMPDEST ::
      PUSH_N "0x007b" ::
      PUSH_N "0x04" ::
      POP ::
      PUSH_N "0x0140" ::
      JUMP ::
      JUMPDEST ::
      STOP ::
      JUMPDEST ::
      PUSH_N "0x008e" ::
      PUSH_N "0x04" ::
      DUP1 ::
      CALLDATALOAD ::
      SWAP1 ::
      PUSH_N "0x20" ::
      ADD ::
      POP ::
      PUSH_N "0x00ad" ::
      JUMP ::
      JUMPDEST ::
      PUSH_N "0x40" ::
      MLOAD ::
      DUP1 ::
      DUP3 ::
      DUP2 ::
      MSTORE :: nil.

  Definition example1_part4 :=
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
      RETURN ::
      JUMPDEST ::
      PUSH_N "0x01" ::
      PUSH_N "0x00" ::
      POP ::
      SLOAD ::
      DUP2 ::
      JUMP ::
      JUMPDEST ::
      PUSH_N "0x00" ::
      PUSH_N "0x00" ::
      PUSH_N "0x00" ::
      SWAP1 ::
      SLOAD ::
      SWAP1 ::
      PUSH_N "0x0100" ::
      EXP ::
      SWAP1 ::
      DIV :: nil.

  Definition example1_part5 :=
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND :: nil.

  Definition example1_part6 :=
      CALLER ::
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      instr_EQ ::
      ISZERO ::
      PUSH_N "0x013a" ::
      JUMPI ::
      TIMESTAMP ::
      DUP3 ::
      GT ::
      DUP1 ::
      ISZERO ::
      PUSH_N "0x0119" ::
      JUMPI ::
      POP ::
      PUSH_N "0x00" ::
      PUSH_N "0x01" ::
      PUSH_N "0x00" ::
      POP ::
      SLOAD ::
      instr_EQ ::
      JUMPDEST ::
      ISZERO ::
      PUSH_N "0x0131" ::
      JUMPI ::
      DUP2 ::
      PUSH_N "0x01" ::
      PUSH_N "0x00" ::
      POP :: nil.

  Definition example1_part7 :=
      DUP2 ::
      SWAP1 ::
      SSTORE ::
      POP ::
      PUSH_N "0x01" ::
      SWAP1 ::
      POP ::
      PUSH_N "0x013b" ::
      JUMP ::
      JUMPDEST ::
      PUSH_N "0x00" ::
      SWAP1 ::
      POP ::
      PUSH_N "0x013b" ::
      JUMP ::
      JUMPDEST ::
      JUMPDEST ::
      SWAP2 ::
      SWAP1 ::
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
      DIV :: nil.

  Definition example1_part8 :=
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      CALLER ::
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      instr_EQ ::
      ISZERO ::
      PUSH_N "0x01df" ::
      JUMPI ::
      PUSH_N "0x01" ::
      PUSH_N "0x00" ::
      POP ::
      SLOAD ::
      TIMESTAMP ::
      GT ::
      ISZERO ::
      PUSH_N "0x01de" ::
      JUMPI ::
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
      SUICIDE :: (* here, payout occurs *)
      JUMPDEST ::
      JUMPDEST ::
      JUMPDEST ::
      JUMP :: nil.

  Definition example1 :=
    example1_part1
    ++ example1_part2
    ++ example1_part3
    ++ example1_part4
    ++ example1_part5
    ++ example1_part6
    ++ example1_part7
    ++ example1_part8.

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
     first,  https://etherchain.org/account/0x3c7771db7f343b79003e8c9ba787bbe47764ed05#codeDisasm
     second, https://etherchain.org/account/0x10ebb6b1607de9c08c61c6f6044b8edc93b8e9c9#codeDisasm
     second, https://etherchain.org/account/0x2935aa0a2d2fbb791622c29eb1c117b65b7a9085#codeDisasm
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

  Definition calldataload (input : U256.t -> U256.t) : operation :=
    one_one_op input.

  Parameter div : U256.t -> U256.t -> U256.t.

  Definition div_op := two_one_op div.
  Definition add_op := two_one_op add.

  (* A question: what happens when dup1 instruction is executed on an empty stack? *)
  (* Do we end up with a stack of length 1?  Answer: No.  See 9.4.2 of the yellow paper. *)

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

  Definition eq : operation := two_one_op
    (fun a b => match U256.compare a b with
                | EQ _ => one
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

  Record state :=
    {   stc     : stack
      ; mem     : memory
      ; str     : memory
      ; program : list instr
      ; prg_sfx : list instr
    }.

  Inductive result :=
  | continue : state -> result
  | suicide  : result
  | returned : result
  | stopped  : result
  | end_of_program :result (* what actually happens? *)
  | failure : result (* what actually happens? *)
  .

  Definition operation_sem (op : operation) (pre: state) : result :=
    match pre.(prg_sfx) with
      | nil => end_of_program
      | _ :: tl =>
        match op pre.(stc) pre.(mem) with
          | None => failure
          | Some (s,m) =>
            continue {| stc := s ;
              mem := m ;
              str := pre.(str) ;
              program := pre.(program);
              prg_sfx := tl |}
        end
    end.

  Definition instr_sem (i : instr) : state -> result :=
    match i with
      | STOP => (fun _ => stopped)
      | ADD => operation_sem add_op
      | SUB => operation_sem sub_op
      | DIV => operation_sem div_op
      | EXP => operation_sem exp_op
      | GT  => operation_sem gt_op
      | instr_EQ => operation_sem eq
      | AND => operation_sem and_op
      | ISZERO => operation_sem izero
      | CALLER => 
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
      | PUSH_N str
      | DUP1
      | DUP2
      | DUP3
      | SWAP1
      | SWAP2
      | RETURN
      | SUICIDE
    end.

End EVM.

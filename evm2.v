Require Import String.
Require Import List.
Require Import FMapInterface.

Module Lang.

  Inductive instr := (** partial.  adding as necessary. *)
  | STOP
  | ADD
  | SUB
  | DIV
  | EXP
  | instr_GT
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

  Search (string -> nat).

  Definition instr_length (i : instr) : nat :=
    match i with
    | PUSH_N str => NPeano.div (String.length str) 2
    | _ => 1
    end.

  Fixpoint drop_bytes (prog : list instr) (bytes : nat) {struct bytes} :=
    match prog, bytes with
    | _, O => prog
    | PUSH_N str :: tl, S pre =>
       drop_bytes tl (pre - (NPeano.div (String.length str) 2 - 1))
    | _ :: tl, S pre =>
      drop_bytes tl pre
    | nil, S _ => nil
    end.

  Definition example1 : list instr :=
      PUSH_N "0x60" :: (* 2 *)
      PUSH_N "0x40" :: (* 4 *)
      MSTORE ::        (* 5 *)
      PUSH_N "0x00" :: (* 7 *)
      CALLDATALOAD ::  (* 8 *)
      PUSH_N "0x0100000000000000000000000000000000000000000000000000000000" :: (* 38 *)
      SWAP1 :: (* 39 *)
      DIV ::   (* 40 *)
      DUP1 ::  (* 41 *)
      PUSH_N "0x4665096d" :: (* 46 *)
      instr_EQ :: (* 47 *)
      PUSH_N "0x004f" :: (* 50 *)
      JUMP :: (* 51 *)
      DUP1 :: (* 52 *)
      PUSH_N "0xbe040fb0" :: (* 57 *)
      instr_EQ :: (* 58 *)
      PUSH_N "0x0070" :: (* 60 *)
      JUMPI :: (* 61 *)
      DUP1 ::  (* 62 *)
      PUSH_N "0xdd467064" :: (* 67 *)
      instr_EQ :: (* 68 *)
      PUSH_N "0x007d" :: (* 71 *)
      JUMPI :: (* 72 *)
      PUSH_N "0x004d" :: (*75 *)
      JUMP :: (* 76 *)
      JUMPDEST :: (* 77 *)
      STOP :: (* 78 *)
      JUMPDEST :: (* 79 *)
      PUSH_N "0x005a" ::
      PUSH_N "0x04" ::
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
      PUSH_N "0x013a" ::
      JUMPI ::
      TIMESTAMP ::
      DUP3 ::
      instr_GT ::
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
      POP ::
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
      PUSH_N "0x01df" ::
      JUMPI ::
      PUSH_N "0x01" ::
      PUSH_N "0x00" ::
      POP ::
      SLOAD ::
      TIMESTAMP ::
      instr_GT ::
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

  Definition calldataload (input : list U256.t) : operation :=
    one_one_op (fun n => List.nth (to_nat n) input zero).

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

  Record state :=
    {   stc     : stack
      ; mem     : memory
      ; str     : memory
      ; prg_sfx : list instr
      ; program : list instr
      ; caller  : U256.t
      ; value   : U256.t
      ; data    : list U256.t
    }.

  Inductive result :=
  | continue : state -> result
  | suicide  : result
  | returned : result
  | stopped  : result
  | end_of_program :result (* what actually happens? *)
  | failure : result (* what actually happens? *)
  | not_implemented :result
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
              prg_sfx := tl;
              caller := pre.(caller);
              value := pre.(value);
              data  := pre.(data)
            |}
        end
    end.

  Definition reader (f : state -> U256.t) (pre : state) : result :=
    match pre.(prg_sfx) with
      | nil => end_of_program
      | _ :: tl =>
        continue {| stc := f pre :: pre.(stc) ;
          mem := pre.(mem) ;
          str := pre.(str) ;
          program := pre.(program);
          prg_sfx := tl;
          caller := pre.(caller);
          value  := pre.(value);
          data   := pre.(data)
        |}
    end.

  Parameter U : string -> U256.t.
  Parameter Ulen : forall {a : Type}, list a -> U256.t.

  Definition instr_sem (i : instr) : state -> result :=
    match i with
      | STOP => (fun _ => stopped)
      | ADD => operation_sem add_op
      | SUB => operation_sem sub_op
      | DIV => operation_sem div_op
      | EXP => operation_sem exp_op
      | instr_GT  => operation_sem gt
      | instr_EQ => operation_sem eq
      | AND => operation_sem and_op
      | ISZERO => operation_sem iszero
      | CALLER => reader caller
      | CALLVALUE => reader value
      | CALLDATALOAD => (fun pre => operation_sem (calldataload pre.(data)) pre)
      | CALLDATASIZE => reader (fun st => Ulen (st.(data)))
      | CALLDATACOPY => (fun pre => operation_sem (calldatacopy pre.(data)) pre)
      | TIMESTAMP => (fun _ => not_implemented)
      | POP =>    operation_sem pop
      | MLOAD  => operation_sem mload
      | MSTORE => operation_sem mstore
      | SLOAD => (fun pre => operation_sem (sload pre.(str)) pre)
      | SSTORE => (fun _ => not_implemented)
      | JUMP => (fun pre =>
                   match pre.(stc) with
                   | nil => failure
                   | hd :: tl =>
                     continue {|
                       stc := tl;
                       mem := pre.(mem);
                       str := pre.(str);
                       program := pre.(program);
                       prg_sfx := drop_bytes pre.(program) (to_nat hd);
                       caller := pre.(caller);
                       value := pre.(value);
                       data := pre.(data)
                     |}
                   end
                )
      | JUMPI => (fun _ => not_implemented)
      | JUMPDEST =>
        (fun pre => match pre.(prg_sfx) with
                      | nil => failure
                      | _ :: tl =>
                        continue {|
                            stc := pre.(stc);
                            mem := pre.(mem);
                            str := pre.(str);
                            program := pre.(program);
                            prg_sfx := tl;
                            caller := pre.(caller);
                            value := pre.(value);
                            data := pre.(data)
                            |}
                    end)
      | PUSH_N str => operation_sem (push_x (U str))
      | DUP1 => operation_sem dup1
      | DUP2 => operation_sem dup2
      | DUP3 => operation_sem dup3
      | SWAP1 => operation_sem swap1
      | SWAP2 => (fun _ => not_implemented)
      | RETURN => (fun _ => not_implemented)
      | SUICIDE => (fun _ => suicide)
    end.

  Fixpoint apply_n (n : nat) (pre : state) : result :=
    match n, pre.(prg_sfx) with
      | O, _ => continue pre
      | S n', hd::_ =>
        match instr_sem hd pre with
          | continue post =>  apply_n n' post
          | x => x
        end
      | S n', nil => end_of_program
    end.

  Lemma apply_S : forall n' pre,
    apply_n (S n') pre =
    match pre.(prg_sfx) with
      | hd :: _ => 
        match instr_sem hd pre with
          | continue post =>  apply_n n' post
          | x => x
        end
      | nil => end_of_program
    end.
  Proof.
  auto.
  Qed.


  Parameter c : U256.t.
  Parameter v : U256.t.
  Parameter d : list U256.t.

  Definition ex := {|
    stc := nil;
    mem := Memory.empty U256.t;
    str := Memory.empty U256.t;
    program := example1;
    prg_sfx := example1;
    caller := c;
    value := v;
    data := d
  |}.

  Parameter tn : (to_nat (U "0x004f")) = 79.
  Parameter hg : (to_nat (U "0x00a4")) = 164.
  Parameter gg : (to_nat (U "0x005a")) = 90.

  Goal apply_n 27 ex <> suicide.
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite tn.
    compute -[apply_n].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite apply_S; compute -[apply_n NPeano.div].

    rewrite apply_S; compute -[apply_n NPeano.div].

    rewrite apply_S; compute -[apply_n NPeano.div].

    rewrite apply_S; compute -[apply_n NPeano.div].
    rewrite hg.

    compute -[apply_n].

    rewrite apply_S; compute -[apply_n].
    rewrite apply_S; compute -[apply_n].
    rewrite apply_S; compute -[apply_n].
    rewrite apply_S; compute -[apply_n].
    rewrite apply_S; compute -[apply_n].
    rewrite apply_S; compute -[apply_n].
    rewrite apply_S; compute -[apply_n].

    rewrite gg.
    congruence.
  Qed.

End EVM.

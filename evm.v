Require Import Coq.Numbers.Natural.Peano.NPeano.

Module Type Impl.
  Parameter bit256 : Set.
  Parameter address : Set.
  Parameter FMap : Set -> Set -> Set. (* XXX: has to be refined *)
End Impl.

Module State (I : Impl).

  Import I.

  (* account state described in 4.1 *)
  Record account_state : Set :=
    {   nonce       : bit256 (* 'scalar' ? *)
      ; balance     : bit256
      ; storageRoot : bit256
      ; codeHash    : bit256
    }.
  Definition world_state := FMap address account_state.
End State.

Module Lang (I : Impl).
  Import I.

  Inductive OpCode : Set :=
  | STOP
  | ADD
  | MUL
  | SUB
  | DIV
  | SDIV
  | MOD
  | SMOD
  | ADDMOD
  | MULMOD
  | EXP
  | SIGNEXTEND
  | LT
  | GT
  | SLT
  | SGT
  | EQ
  | ISZERO
  | AND
  | OR
  | XOR
  | NOT
  | BYTE
  | SHA3
  | ADDRESS
  | BALANCE
  | ORIGIN
  | CALLER
  | CALLVALUE
  | CALLDATALOAD
  | CALLDATASIZE
  | CALLDATACOPY
  | CODESIZE
  | CODECOPY
  | GASPRICE
  | EXTCODESIZE
  | EXTCODECOPY
  | BLOCKHASH
  | COINBASE
  | TIMESTAMP
  | NUMBER
  | DIFFICULTY
  | GASLIMIT
  | POP
  | MLOAD
  | MSTORE
  | MSTORE8
  | SLOAD
  | SSTORE
  | JUMP
  | JUMPI
  | PC
  | MSIZE
  | GAS
  | JUMPDEST
  | PUSH : nat -> OpCode (* XXX: need to exclude too big arguments *)
  | DUP : nat -> OpCode
  | SWAP : nat -> OpCode
  | LOG : nat -> OpCode
  | CREATE
  | CALL
  | CALLCODE
  | RETURN
  | SUICIDE
  | Number : bit256 -> OpCode
.

  (* what is an RLP? *)
  (* what is the intrinsic gas of a transaction? *)
(* define validity of transaction by (59) *)

    (* now, maybe, read the cpp implementation *)
End Lang.

  (* define substate *)

Module EVM (I : Impl).

  Import I.

  (* 9.4.1 *)
  Record state := {
    state_g  : bit256 ;
    state_pc : bit256 ;
    state_m  : FMap bit256 bit256;
    state_i  : bit256 ;
    state_stack : list bit256
    (* something more *)
    }.

  Definition invariant (s : state) : bool :=
    length s.(state_stack) <=? 256.

  (* what is the type of one-step *)
  Definition step : (s : state) : state.

  (* what is the type of the whole execution? *)

End EVM.

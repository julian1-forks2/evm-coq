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
  | SDIV
  | MOD
  | SMOD
  | ADDMOD
  | MULMOD
  | SIGNEXTEND
  | EXP
  | GT
  | SGT
  | EQ
  | LT
  | SLT
  | AND
  | OR
  | XOR
  | NOT
  | BYTE
  | ISZERO
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
  | DUP10
  | DUP11
  | DUP12
  | DUP13
  | DUP14
  | DUP15
  | DUP16
  | SWAP1
  | SWAP2
  | SWAP3
  | SWAP4
  | SWAP5
  | SWAP6
  | SWAP7
  | SWAP8
  | SWAP9
  | SWAP10
  | SWAP11
  | SWAP12
  | SWAP13
  | SWAP14
  | SWAP15
  | SWAP16
  | LOG0
  | LOG1
  | LOG2
  | LOG3
  | LOG4
  | CREATE
  | CALL
  | CALLCODE
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

  Require Import Coq.Program.Wf.

  Fixpoint drop_bytes (prog : list instr) (bytes : nat) {struct bytes} :=
    match prog, bytes with
    | _, O => prog
    | PUSH_N str :: tl, S pre =>
      drop_bytes tl (pre - (string_half_len str - 1))
    | _ :: tl, S pre =>
      drop_bytes tl pre
    | nil, S _ => nil
    end.

  Inductive decoding_mode : Set :=
  | first_zero
  | first_x
  | next_instr
  | read_0
  | read_1
  | read_2
  | read_3
  | read_4
  | read_5
  | read_6
  | read_7
  | read_8
  | read_9
  | read_a
  | read_b
  | read_c
  | read_d
  | read_e
  | read_f
  | read_hex : nat (* remaining read, after the next char *)
               -> nat (* read so far *) -> decoding_mode
  .

  Inductive decode_result : Set :=
  | success : list instr -> decode_result
  | failure : string     -> decode_result
  .

  (* sofar accumulates instrucitons in the reverse order *)

  Fixpoint decode_inner (str : string) (m : decoding_mode)
           (sofar : list instr): decode_result :=
  match m with
  | first_zero =>
    match str with
    | String "0" rest => decode_inner rest first_x sofar
    | _ => failure "first nonzero"
    end
  | first_x =>
    match str with
    | String "x" rest => decode_inner rest next_instr sofar
    | _ => failure "second not x"
    end
  | next_instr =>
    match str with
    | String "0" rest => decode_inner rest read_0 sofar
    | String "1" rest => decode_inner rest read_1 sofar
    | String "2" rest => decode_inner rest read_2 sofar
    | String "3" rest => decode_inner rest read_3 sofar
    | String "4" rest => decode_inner rest read_4 sofar
    | String "5" rest => decode_inner rest read_5 sofar
    | String "6" rest => decode_inner rest read_6 sofar
    | String "7" rest => decode_inner rest read_7 sofar
    | String "8" rest => decode_inner rest read_8 sofar
    | String "9" rest => decode_inner rest read_9 sofar
    | String "a" rest => decode_inner rest read_a sofar
    | String "b" rest => decode_inner rest read_b sofar
    | String "c" rest => decode_inner rest read_c sofar
    | String "d" rest => decode_inner rest read_d sofar
    | String "e" rest => decode_inner rest read_e sofar
    | String "f" rest => decode_inner rest read_f sofar
    | EmptyString => success (List.rev sofar)
    | _ => failure "?"
    end
  | read_0 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (STOP :: sofar)
    | String "1" rest => decode_inner rest next_instr (ADD  :: sofar)
    | String "2" rest => decode_inner rest next_instr (MUL  :: sofar)
    | String "3" rest => decode_inner rest next_instr (SUB  :: sofar)
    | String "4" rest => decode_inner rest next_instr (DIV  :: sofar)
    | String "5" rest => decode_inner rest next_instr (SDIV :: sofar)
    | String "6" rest => decode_inner rest next_instr (MOD  :: sofar)
    | String "7" rest => decode_inner rest next_instr (SMOD :: sofar)
    | String "8" rest => decode_inner rest next_instr (ADDMOD :: sofar)
    | String "9" rest => decode_inner rest next_instr (MULMOD :: sofar)
    | String "a" rest => decode_inner rest next_instr (EXP :: sofar)
    | String "b" rest => decode_inner rest next_instr (SIGNEXTEND :: sofar)
    | String "c" rest => failure "0c"
    | String "d" rest => failure "0d"
    | String "e" rest => failure "0e"
    | String "f" rest => failure "0f"
    | _ => failure "0?"
    end
  | read_1 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (LT     :: sofar)
    | String "1" rest => decode_inner rest next_instr (GT     :: sofar)
    | String "2" rest => decode_inner rest next_instr (SLT    :: sofar)
    | String "3" rest => decode_inner rest next_instr (SGT    :: sofar)
    | String "4" rest => decode_inner rest next_instr (EQ     :: sofar)
    | String "5" rest => decode_inner rest next_instr (ISZERO :: sofar)
    | String "6" rest => decode_inner rest next_instr (AND    :: sofar)
    | String "7" rest => decode_inner rest next_instr (OR     :: sofar)
    | String "8" rest => decode_inner rest next_instr (XOR    :: sofar)
    | String "9" rest => decode_inner rest next_instr (NOT    :: sofar)
    | String "a" rest => decode_inner rest next_instr (BYTE   :: sofar)
    | String "b" rest => failure "1b"
    | String "c" rest => failure "1c"
    | String "d" rest => failure "1d"
    | String "e" rest => failure "1e"
    | String "f" rest => failure "1f"
    | _ => failure "1?"
    end
  | read_2 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (SHA3  :: sofar)
    | _ => failure "2?"
    end
  | read_3 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (ADDRESS :: sofar)
    | String "1" rest => decode_inner rest next_instr (BALANCE :: sofar)
    | String "2" rest => decode_inner rest next_instr (ORIGIN :: sofar)
    | String "3" rest => decode_inner rest next_instr (CALLER :: sofar)
    | String "4" rest => decode_inner rest next_instr (CALLVALUE :: sofar)
    | String "5" rest => decode_inner rest next_instr (CALLDATALOAD :: sofar)
    | String "6" rest => decode_inner rest next_instr (CALLDATASIZE :: sofar)
    | String "7" rest => decode_inner rest next_instr (CALLDATACOPY :: sofar)
    | String "8" rest => decode_inner rest next_instr (CODESIZE :: sofar)
    | String "9" rest => decode_inner rest next_instr (CODECOPY :: sofar)
    | String "a" rest => decode_inner rest next_instr (GASPRICE :: sofar)
    | String "b" rest => decode_inner rest next_instr (EXTCODESIZE :: sofar)
    | String "c" rest => decode_inner rest next_instr (EXTCODECOPY :: sofar)
    | String "d" rest => failure "3d"
    | String "e" rest => failure "3e"
    | String "f" rest => failure "3f"
    | _ => failure "3?"
    end
  | read_4 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (BLOCKHASH :: sofar)
    | String "1" rest => decode_inner rest next_instr (COINBASE :: sofar)
    | String "2" rest => decode_inner rest next_instr (TIMESTAMP :: sofar)
    | String "3" rest => decode_inner rest next_instr (NUMBER :: sofar)
    | String "4" rest => decode_inner rest next_instr (DIFFICULTY :: sofar)
    | String "5" rest => decode_inner rest next_instr (GASLIMIT :: sofar)
    | String "6" rest => failure "46"
    | String "7" rest => failure "47"
    | String "8" rest => failure "48"
    | String "9" rest => failure "49"
    | String "a" rest => failure "4a"
    | String "b" rest => failure "4b"
    | String "c" rest => failure "4c"
    | String "d" rest => failure "4d"
    | String "e" rest => failure "4e"
    | String "f" rest => failure "4f"
    | _ => failure "4?"
    end
  | read_5 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (POP :: sofar)
    | String "1" rest => decode_inner rest next_instr (MLOAD :: sofar)
    | String "2" rest => decode_inner rest next_instr (MSTORE :: sofar)
    | String "3" rest => decode_inner rest next_instr (MSTORE8 :: sofar)
    | String "4" rest => decode_inner rest next_instr (SLOAD :: sofar)
    | String "5" rest => decode_inner rest next_instr (SSTORE :: sofar)
    | String "6" rest => decode_inner rest next_instr (JUMP :: sofar)
    | String "7" rest => decode_inner rest next_instr (JUMPI :: sofar)
    | String "8" rest => decode_inner rest next_instr (PC :: sofar)
    | String "9" rest => decode_inner rest next_instr (MSIZE :: sofar)
    | String "a" rest => decode_inner rest next_instr (GAS :: sofar)
    | String "b" rest => decode_inner rest next_instr (JUMPDEST :: sofar)
    | String "c" rest => failure "5c"
    | String "d" rest => failure "5d"
    | String "e" rest => failure "5e"
    | String "f" rest => failure "5f"
    | _ => failure "5?"
    end
  | read_6 =>
    match str with
    | String "0" rest => decode_inner rest (read_hex 2 0)  sofar
    | String "1" rest => decode_inner rest (read_hex 4 0)  sofar
    | String "2" rest => decode_inner rest (read_hex 6 0)  sofar
    | String "3" rest => decode_inner rest (read_hex 8 0)  sofar
    | String "4" rest => decode_inner rest (read_hex 10 0) sofar
    | String "5" rest => decode_inner rest (read_hex 12 0) sofar
    | String "6" rest => decode_inner rest (read_hex 14 0) sofar
    | String "7" rest => decode_inner rest (read_hex 16 0) sofar
    | String "8" rest => decode_inner rest (read_hex 18 0) sofar
    | String "9" rest => decode_inner rest (read_hex 20 0) sofar
    | String "a" rest => decode_inner rest (read_hex 22 0) sofar
    | String "b" rest => decode_inner rest (read_hex 24 0) sofar
    | String "c" rest => decode_inner rest (read_hex 26 0) sofar
    | String "d" rest => decode_inner rest (read_hex 28 0) sofar
    | String "e" rest => decode_inner rest (read_hex 30 0) sofar
    | String "f" rest => decode_inner rest (read_hex 32 0) sofar
    | _ => failure "6?"
    end
  | read_7 =>
    match str with
    | String "0" rest => decode_inner rest (read_hex 34 0) sofar
    | String "1" rest => decode_inner rest (read_hex 36 0) sofar
    | String "2" rest => decode_inner rest (read_hex 38 0) sofar
    | String "3" rest => decode_inner rest (read_hex 40 0) sofar
    | String "4" rest => decode_inner rest (read_hex 42 0) sofar
    | String "5" rest => decode_inner rest (read_hex 44 0) sofar
    | String "6" rest => decode_inner rest (read_hex 46 0) sofar
    | String "7" rest => decode_inner rest (read_hex 48 0) sofar
    | String "8" rest => decode_inner rest (read_hex 50 0) sofar
    | String "9" rest => decode_inner rest (read_hex 52 0) sofar
    | String "a" rest => decode_inner rest (read_hex 54 0) sofar
    | String "b" rest => decode_inner rest (read_hex 56 0) sofar
    | String "c" rest => decode_inner rest (read_hex 58 0) sofar
    | String "d" rest => decode_inner rest (read_hex 60 0) sofar
    | String "e" rest => decode_inner rest (read_hex 62 0) sofar
    | String "f" rest => decode_inner rest (read_hex 64 0) sofar
    | _ => failure "7?"
    end
  | read_8 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (DUP1  :: sofar)
    | String "1" rest => decode_inner rest next_instr (DUP2  :: sofar)
    | String "2" rest => decode_inner rest next_instr (DUP3  :: sofar)
    | String "3" rest => decode_inner rest next_instr (DUP4  :: sofar)
    | String "4" rest => decode_inner rest next_instr (DUP5  :: sofar)
    | String "5" rest => decode_inner rest next_instr (DUP6  :: sofar)
    | String "6" rest => decode_inner rest next_instr (DUP7  :: sofar)
    | String "7" rest => decode_inner rest next_instr (DUP8  :: sofar)
    | String "8" rest => decode_inner rest next_instr (DUP9  :: sofar)
    | String "9" rest => decode_inner rest next_instr (DUP10 :: sofar)
    | String "a" rest => decode_inner rest next_instr (DUP11 :: sofar)
    | String "b" rest => decode_inner rest next_instr (DUP12 :: sofar)
    | String "c" rest => decode_inner rest next_instr (DUP13 :: sofar)
    | String "d" rest => decode_inner rest next_instr (DUP14 :: sofar)
    | String "e" rest => decode_inner rest next_instr (DUP15 :: sofar)
    | String "f" rest => decode_inner rest next_instr (DUP16 :: sofar)
    | _ => failure "8?"
    end
  | read_9 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (SWAP1  :: sofar)
    | String "1" rest => decode_inner rest next_instr (SWAP2  :: sofar)
    | String "2" rest => decode_inner rest next_instr (SWAP3  :: sofar)
    | String "3" rest => decode_inner rest next_instr (SWAP4  :: sofar)
    | String "4" rest => decode_inner rest next_instr (SWAP5  :: sofar)
    | String "5" rest => decode_inner rest next_instr (SWAP6  :: sofar)
    | String "6" rest => decode_inner rest next_instr (SWAP7  :: sofar)
    | String "7" rest => decode_inner rest next_instr (SWAP8  :: sofar)
    | String "8" rest => decode_inner rest next_instr (SWAP9  :: sofar)
    | String "9" rest => decode_inner rest next_instr (SWAP10 :: sofar)
    | String "a" rest => decode_inner rest next_instr (SWAP11 :: sofar)
    | String "b" rest => decode_inner rest next_instr (SWAP12 :: sofar)
    | String "c" rest => decode_inner rest next_instr (SWAP13 :: sofar)
    | String "d" rest => decode_inner rest next_instr (SWAP14 :: sofar)
    | String "e" rest => decode_inner rest next_instr (SWAP15 :: sofar)
    | String "f" rest => decode_inner rest next_instr (SWAP16 :: sofar)
    | _ => failure "9?"
    end
  | read_a =>
    match str with
    | String "0" rest => decode_inner rest next_instr (LOG0 :: sofar)
    | String "1" rest => decode_inner rest next_instr (LOG1 :: sofar)
    | String "2" rest => decode_inner rest next_instr (LOG2 :: sofar)
    | String "3" rest => decode_inner rest next_instr (LOG3 :: sofar)
    | String "4" rest => decode_inner rest next_instr (LOG4 :: sofar)
    | String "5" rest => failure "a5"
    | String "6" rest => failure "a6"
    | String "7" rest => failure "a7"
    | String "8" rest => failure "a8"
    | String "9" rest => failure "a9"
    | String "a" rest => failure "aa"
    | String "b" rest => failure "ab"
    | String "c" rest => failure "ac"
    | String "d" rest => failure "ad"
    | String "e" rest => failure "ae"
    | String "f" rest => failure "af"
    | _ => failure "a?"
    end
  | read_b => failure "b?"
  | read_c => failure "c?"
  | read_d => failure "d?"
  | read_e => failure "e?"
  | read_f =>
    match str with
    | String "0" rest => decode_inner rest next_instr (LOG0 :: sofar)
    | String "1" rest => decode_inner rest next_instr (LOG1 :: sofar)
    | String "2" rest => decode_inner rest next_instr (LOG2 :: sofar)
    | String "3" rest => decode_inner rest next_instr (LOG3 :: sofar)
    | String "4" rest => failure "f4"
    | String "5" rest => failure "f5"
    | String "6" rest => failure "f6"
    | String "7" rest => failure "f7"
    | String "8" rest => failure "f8"
    | String "9" rest => failure "f9"
    | String "a" rest => failure "fa"
    | String "b" rest => failure "fb"
    | String "c" rest => failure "fc"
    | String "d" rest => failure "fd"
    | String "e" rest => failure "fe"
    | String "f" rest => decode_inner rest next_instr (SUICIDE :: sofar)
    | _ => failure "f?"
    end
  |_ => failure "decode not implemented"
  end
  .


(*
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
    EQ ::
    PUSH_N "0x00aa" ::
    JUMPI ::
    DUP1 ::
    PUSH_N "0x6042a760" ::
    EQ ::
    PUSH_N "0x00c9" ::
    JUMPI ::
    DUP1 ::
    PUSH_N "0xb214faa5" ::
    EQ ::
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
    EQ ::
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
    EQ ::
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
    JUMP :: nil. *)

End Lang.

Require Import Equalities.

Module EVM (U256:DecidableTypeFull).

  Import Lang.

  Parameter Uzero : U256.t.
  Parameter Uone  : U256.t.
  Parameter Usucc : U256.t -> U256.t.
  Parameter Uto_nat : U256.t -> nat.
  Parameter Usub : U256.t -> U256.t -> U256.t.
  Parameter Uadd : U256.t -> U256.t -> U256.t.
  Parameter Uand : U256.t -> U256.t -> U256.t.
  Parameter Uexp : U256.t -> U256.t -> U256.t.
  Parameter Udiv : U256.t -> U256.t -> U256.t.
  Parameter Umul : U256.t -> U256.t -> U256.t.
  Parameter Ugt  : U256.t -> U256.t -> bool.


  Definition stack := list U256.t.

  Require Import FMapWeakList.

  Module Memory := Make (U256).

  Definition memory := Memory.t U256.t.

  Definition m T := option (T * memory).

  Definition operation := stack -> memory -> m stack (* maybe with side-effect? *).

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
          Some (match Memory.find addr mem with Some b => b | None => Uzero end :: l, mem)
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
        memwrite_n (Usucc start_addr (* what happens when this overflows? *) ) len'
        (match source with nil => nil | _ :: tl => tl end)
        (Memory.add start_addr (match source with nil => Uzero | hd :: _ => hd end) mem)
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
          Some (l, memwrite_n m0 (Uto_nat m2) (drop (Uto_nat m1) input) mem)
        | _ => None
      end.

  Definition iszero : operation :=
    fun s mem =>
      match s with
        | nil => None
        | h :: tl =>
          Some ((if U256.eqb Uzero h then Uone else Uzero) :: tl, mem)
      end.

  Definition two_two_op (f : U256.t -> U256.t -> (U256.t * U256.t)) : operation :=
    fun s mem =>
      match s with
        | a :: b :: l =>
          Some (fst (f a b) :: snd (f a b) :: l, mem)
        | _ => None
      end.

  Definition two_one_op (f : U256.t -> U256.t -> U256.t) : operation :=
    fun s mem =>
      match s with
        | nil => None
        | _ :: nil => None
        | a :: b :: l => Some ((f a b) :: l, mem)
      end.

  Definition exp_op : operation := two_one_op Uexp.

  Definition and_op : operation := two_one_op Uand.

  Definition one_one_op (f : U256.t -> U256.t) : operation :=
    fun s mem =>
      match s with
        | nil => None
        | a :: l => Some (f a :: l, mem)
      end.

  Definition sload storage : operation :=
    one_one_op (fun addr => match Memory.find addr storage with Some b => b | None => Uzero end).

  Definition calldataload (input : list U256.t) : operation :=
    one_one_op (fun n => List.nth (Uto_nat n) input Uzero).



  Definition div_op := two_one_op Udiv.
  Definition mul_op := two_one_op Umul.
  Definition add_op := two_one_op Uadd.

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
    (fun a b => if U256.eqb a b then Uone else Uzero).

  Definition gt : operation := two_one_op
    (fun a b => if Ugt a b then Uone else Uzero).

  Definition sub_op : operation := two_one_op Usub.

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
  | not_implemented : instr -> state -> result
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
      | SDIV => (fun pre => not_implemented SDIV pre)
      | MOD => (fun pre => not_implemented MOD pre)
      | SMOD => (fun pre => not_implemented SMOD pre)
      | ADDMOD => (fun pre => not_implemented ADDMOD pre)
      | MULMOD => (fun pre => not_implemented MULMOD pre)
      | SIGNEXTEND => not_implemented i
      | EXP => operation_sem exp_op
      | GT  => operation_sem gt
      | LT  => not_implemented i
      | SLT => not_implemented i
      | SGT => not_implemented i
      | EQ => operation_sem eq_op
      | AND => operation_sem and_op
      | OR  => not_implemented i
      | XOR => not_implemented i
      | NOT => not_implemented i
      | BYTE => not_implemented i
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
                       prg_sfx := drop_bytes pre.(program) (Uto_nat hd);
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
                      if U256.eqb Uzero cond then
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
                            prg_sfx := drop_bytes pre.(program) (Uto_nat dst);
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
      | CALL => (fun pre => not_implemented CALL pre)
      | RETURN => returned
      | SUICIDE => (fun pre =>
                      match pre.(stc) with
                        | nil => failure pre
                        | hd :: _ => suicide hd
                      end
                   )
      | _ => not_implemented i
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
  Proof. by []. Qed.

  Lemma eqeq : forall x, U256.eqb x x.
  Proof. by move=> ?; rewrite/is_true U256.eqb_eq. Qed.

  Parameter somebody : U256.t.

  Parameter caller_ex1 : U256.t.
  Parameter value_ex1 : U256.t.
  Parameter data_ex1 : list U256.t.
  Parameter current_time : U256.t.
  Parameter store_init : Memory.t U256.t.

Definition example1 : list instr :=
      PUSH_N "0x60" ::
      PUSH_N "0x40" ::
      MSTORE ::
      PUSH_N "0x00" ::
      CALLDATALOAD ::
      PUSH_N "0x0100000000000000000000000000000000000000000000000000000000" ::
      SWAP1 ::
      DIV ::
      DUP1 ::
      PUSH_N "0x4665096d" ::
      EQ ::
      PUSH_N "0x004f" ::
      JUMPI ::
      DUP1 ::
      PUSH_N "0xbe040fb0" ::
      EQ ::
      PUSH_N "0x0070" ::
      JUMPI ::
      DUP1 ::
      PUSH_N "0xdd467064" ::
      EQ ::
      PUSH_N "0x007d" ::
      JUMPI ::
      PUSH_N "0x004d" ::
      JUMP ::
      JUMPDEST ::
      STOP ::
      JUMPDEST ::
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
      EQ ::
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
      EQ ::
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
      EQ ::
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


  (* This results in a normal return. *)
  (* Maybe the execution can start in the middle.  How? *)
  Definition ex := {|
    stc := nil;
    mem := Memory.empty U256.t;
    str := store_init;
    program := example1;
    prg_sfx := example1;
    caller := caller_ex1;
    value := value_ex1;
    data := data_ex1;
    time := current_time;
    noise := initial_noise
  |}.


  Definition interesting (r : result) (target : U256.t) :=
    match r with
      | continue _ => False
      | suicide _  => True
      | returned st
      | stopped st  =>
        store_init <> st.(str) /\ Memory.find Uzero st.(str) = Some target
      | failure _ => True
      | end_of_program _ => True
      | not_implemented _ _ => True
    end.

  Require Import Ascii.

  Open Scope char_scope.
  Print string.

  Definition read_hex_char (c : ascii) : option nat :=
    match c with
    | "0" => Some 0
    | "1" => Some 1
    | "2" => Some 2
    | "3" => Some 3
    | "4" => Some 4
    | "5" => Some 5
    | "6" => Some 6
    | "7" => Some 7
    | "8" => Some 8
    | "9" => Some 9
    | "a" => Some 10
    | "b" => Some 11
    | "c" => Some 12
    | "d" => Some 13
    | "e" => Some 14
    | "f" => Some 15
    | _   => None
    end.


  Fixpoint read_hex (carry: nat) (str : string) : nat :=
    match str with
    | EmptyString => carry
    | String c rest =>
      match read_hex_char c with
      | None => 0
      | Some num => read_hex (carry * 16 + num) rest
      end
    end.

  Definition literal_to_nat (str : string) : nat :=
    match str with
    | String "0" (String "x" rest) => read_hex 0 rest
    | _ => 0
    end.

  Parameter Uliteral : forall str,
      (Uto_nat (U str)) = literal_to_nat str.

  Lemma dropUlit :
    forall str x,
      drop_bytes x (Uto_nat (U str)) = drop_bytes x (literal_to_nat str).
  Proof. by move=> ? ?; rewrite Uliteral. Qed.

  Ltac step := rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting find Memory.find Memory.add]; rewrite ?dropUlit; compute [drop_bytes string_half_len minus literal_to_nat read_hex read_hex_char plus mult].

  Ltac run := repeat step.

  Ltac solve_jump :=
    rewrite dropUlit ;
    compute [drop_bytes string_half_len minus literal_to_nat read_hex read_hex_char plus mult].

  Unset Ltac Debug.

  Goal interesting (apply_n 1000 ex) somebody -> False.
    rewrite/ex/example1.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.

    set b0 := U256.eqb _ _.
    case_eq b0 => b0_eq.
    {
      run.
      set b1 := U256.eqb _ _.
      case_eq b1 => b1_eq.
      {
        run.
        set b2 := U256.eqb _ _.
        case_eq b2 => b2_eq.
        {
          run.
          rewrite/interesting/str.
          case => ? _; done.
        }
        {
          run.
          set b3 := U256.eqb _ _.
          case_eq b3 => b3_eq; run.
          {
            set b4 := U256.eqb _ _.
            case_eq b4 => b4_eq; run.
            {
              set b5 := U256.eqb _ _.
              case_eq b5 => b5_eq.
              {
                run.
                rewrite/interesting.
                rewrite/str.
                move => [_].

(* Stop here to see the conditions for storage[1] change:

  b0 := is_zero
          match
            U256.compare (U "0x4665096d")
              (div (nth (to_nat (U "0x00")) d zero)
                 (U
                    "0x0100000000000000000000000000000000000000000000000000000000"))
          with
          | LT _ => zero
          | EQ _ => one
          | GT _ => zero
          end : bool
  b0_eq : b0 = true
  "input[0] <> ..."

  b1 := is_zero
          match
            U256.compare (U "0xbe040fb0")
              (div (nth (to_nat (U "0x00")) d zero)
                 (U
                    "0x0100000000000000000000000000000000000000000000000000000000"))
          with
          | LT _ => zero
          | EQ _ => one
          | GT _ => zero
          end : bool
  b1_eq : b1 = true
  "input[0] <> ..."

  b2 := is_zero
          match
            U256.compare (U "0xdd467064")
              (div (nth (to_nat (U "0x00")) d zero)
                 (U
                    "0x0100000000000000000000000000000000000000000000000000000000"))
          with
          | LT _ => zero
          | EQ _ => one
          | GT _ => zero
          end : bool
  b2_eq : b2 = false

  "input[0] begins with 0xdd467064".



  K : to_nat (U "0x007d") = 125
  b3 := is_zero
          (if is_zero
                match
                  U256.compare
                    (and (U "0xffffffffffffffffffffffffffffffffffffffff")
                       c)
                    (and (U "0xffffffffffffffffffffffffffffffffffffffff")
                       (and
                          (U "0xffffffffffffffffffffffffffffffffffffffff")
                          (div
                             match
                               (fix find (k : U256.t)
                                         (s : list (U256.t * U256.t))
                                         {struct s} : 
                                option U256.t :=
                                  match s with
                                  | nil => None
                                  | (k', x) :: s' =>
                                      match U256.compare k k' with
                                      | LT _ => None
                                      | EQ _ => Some x
                                      | GT _ => find k s'
                                      end
                                  end) (U "0x00")
                                 (let (this, _) := s in this)
                             with
                             | Some b => b
                             | None => zero
                             end (exp (U "0x0100") (U "0x00")))))
                with
                | LT _ => zero
                | EQ _ => one
                | GT _ => zero
                end
           then one
           else zero) : bool
  b3_eq : b3 = true
  "caller == storage[0]"

  b4 := is_zero
          (if is_zero
                match
                  U256.compare (nth (to_nat (U "0x04")) d zero)
                    current_time
                with
                | LT _ => zero
                | EQ _ => zero
                | GT _ => one
                end
           then one
           else zero) : bool
  b4_eq : b4 = true
  "input[4] > current_time"


  b5 := is_zero
          (if is_zero
                match
                  U256.compare
                    match
                      (fix find (k : U256.t) (s : list (U256.t * U256.t))
                                {struct s} : option U256.t :=
                         match s with
                         | nil => None
                         | (k', x) :: s' =>
                             match U256.compare k k' with
                             | LT _ => None
                             | EQ _ => Some x
                             | GT _ => find k s'
                             end
                         end) (U "0x01") (let (this, _) := s in this)
                    with
                    | Some b => b
                    | None => zero
                    end (U "0x00")
                with
                | LT _ => zero
                | EQ _ => one
                | GT _ => zero
                end
           then one
           else zero) : bool
  b5_eq : b5 = true

  "storage[1] == 0"

*)


                (* storage[1] = input[4] *)
                (* storage at zero has not changed *)
                admit.
              }
              {
                run.
                rewrite/interesting/str.

                case => ? _.
                done.
              }
            }
            {
              run.
              rewrite-/b4.
              rewrite b4_eq.
              run.
              rewrite/interesting/str.
              by case => ? _.
            }
          }
          {
            run.
            rewrite/interesting/str.
            by move => [? _].
          }
        }
      }
      {
        run.
        run.
        set b7 := U256.eqb _ _.
        case_eq b7 => b7_eq.
        {
          run.
          set b8 := U256.eqb _ _.
          case_eq b8 => b8_eq.
          {
            run.

            have -> : (U "0x00") = Uzero by admit.
            have -> : forall x, (Uexp x Uzero) = Uone by admit.
            have -> : forall y, (Udiv y Uone)  = y   by admit.
            (* inheritor is find zero s *)

            idtac.

(*
  Stop here to see the conditions for `SUICIDE` to happen.

  b0 := is_zero
          match
            U256.compare (U "0x4665096d")
              (div (nth (to_nat (U "0x00")) d zero)
                 (U
                    "0x0100000000000000000000000000000000000000000000000000000000"))
          with
          | LT _ => zero
          | EQ _ => one
          | GT _ => zero
          end : bool
  b0_eq : b0 = true
  "input[0] <> ..."


  b1 := is_zero
          match
            U256.compare (U "0xbe040fb0")
              (div (nth (to_nat (U "0x00")) d zero)
                 (U
                    "0x0100000000000000000000000000000000000000000000000000000000"))
          with
          | LT _ => zero
          | EQ _ => one
          | GT _ => zero
          end : bool
  b1_eq : b1 = false
  "input[0] begins with 0xbe040fb0"


  b7 := is_zero
          (if is_zero
                match
                  U256.compare
                    (and (U "0xffffffffffffffffffffffffffffffffffffffff")
                       c)
                    (and (U "0xffffffffffffffffffffffffffffffffffffffff")
                       (and
                          (U "0xffffffffffffffffffffffffffffffffffffffff")
                          (div
                             match
                               (fix find (k : U256.t)
                                         (s : list (U256.t * U256.t))
                                         {struct s} : 
                                option U256.t :=
                                  match s with
                                  | nil => None
                                  | (k', x) :: s' =>
                                      match U256.compare k k' with
                                      | LT _ => None
                                      | EQ _ => Some x
                                      | GT _ => find k s'
                                      end
                                  end) (U "0x00")
                                 (let (this, _) := s in this)
                             with
                             | Some b => b
                             | None => zero
                             end (exp (U "0x0100") (U "0x00")))))
                with
                | LT _ => zero
                | EQ _ => one
                | GT _ => zero
                end
           then one
           else zero) : bool
  b7_eq : b7 = true
  "storage[0] == caller"


  b8 := is_zero
          (if is_zero
                match
                  U256.compare current_time
                    match
                      (fix find (k : U256.t) (s : list (U256.t * U256.t))
                                {struct s} : option U256.t :=
                         match s with
                         | nil => None
                         | (k', x) :: s' =>
                             match U256.compare k k' with
                             | LT _ => None
                             | EQ _ => Some x
                             | GT _ => find k s'
                             end
                         end) (U "0x01") (let (this, _) := s in this)
                    with
                    | Some b => b
                    | None => zero
                    end
                with
                | LT _ => zero
                | EQ _ => zero
                | GT _ => one
                end
           then one
           else zero) : bool
  b8_eq : b8 = true
  "current time > storage[1]"
 *)


            (* stop here and see the condition for SUICIDE *)
            (* next question.  how to change the storage? *)
            admit.
          }
          {
            run.
            rewrite/interesting/str.
            case => ? _; done.
          }
        }
        {
          run.
          rewrite/interesting/str.
          case => ? _; done.
        }
      }
    }
    {
      run.
      rewrite/interesting/str.
      case => ? _; done.
    }
  Qed.

End EVM.

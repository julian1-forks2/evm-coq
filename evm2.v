Require Import FMapInterface.

Module EVM (U256:OrderedType).

  Definition stack := list U256.t.

  Definition state := stack.

  Require Import FMapList.

  Module Memory := Make (U256).

  Definition memory := Memory.t U256.t.

  Definition m T := option (T * memory).

  Definition operation := state -> memory -> m state (* maybe with side-effect? *).

  (* trying to encode
     https://etherchain.org/account/0x2935aa0a2d2fbb791622c29eb1c117b65b7a9085#codeDisasm
  *)

  Require Import List.

  Definition push1 (d : U256.t) : operation :=
    fun s mem => Some (d :: s, mem).

  Definition mstore : operation :=
    fun s mem =>
      match s with
        | nil => None
        | _ :: nil => None
        | a :: b :: l => Some (l, Memory.add a b mem)
      end.

  Definition calldatasize size : operation :=
    fun s mem => Some (size :: s, mem).

  Parameter is_zero : U256.t -> bool.
  Parameter zero : U256.t.
  Parameter one  : U256.t.

  Definition iszero : operation :=
    fun s mem =>
      match s with
        | nil => None
        | h :: tl =>
          Some ((if is_zero h then one else zero) :: tl, mem)
      end.

  Parameter exp : U256.t -> U256.t -> U256.t.

  Definition exp_op : operation :=
    fun s mem =>
      match s with
        | nil => None
        | _ :: nil => None
        | a :: b :: l => Some ((exp a b) :: l, mem)
      end.

  Definition one_one_op (f : U256.t -> U256.t) : operation :=
    fun s mem =>
      match s with
        | nil => None
        | a :: l => Some (f a :: l, mem)
      end.

  Definition calldataload (input : U256.t -> U256.t) : operation :=
    one_one_op input.

  Parameter div : U256.t -> U256.t -> U256.t.

  Definition two_one_op (f : U256.t -> U256.t -> U256.t) : operation :=
    fun s mem =>
      match s with
        | nil => None
        | _ :: nil => None
        | a :: b :: l => Some ((f a b) :: l, mem)
      end.

  Definition div_op := two_one_op div.

  Definition dup2 : operation :=
    fun s mem =>
      match s with
        | a :: b :: l => Some (b :: a :: b :: l, mem)
        | _ => None
      end.

  Definition eq : operation := two_one_op
    (fun a b => match U256.compare a b with
                | EQ _ => one
                | _ => zero
              end).

  Definition two_two_op (f : U256.t -> U256.t -> (U256.t * U256.t)) : operation :=
    fun s mem =>
      match s with
        | a :: b :: l =>
          Some (fst (f a b) :: snd (f a b) :: l, mem)
        | _ => None
      end.

  Definition swap1 : operation := two_two_op (fun a b => (b, a)).

End Evm.


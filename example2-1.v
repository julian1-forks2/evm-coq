Require Import Evm2.

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
      instr_EQ ::
      PUSH_N "0x004f" ::
      JUMPI ::
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
          have -> : (to_nat (U "0x004d")) = 77 by admit.
          compute [drop_bytes string_half_len minus].
          run.
          rewrite/interesting/str.
          case => ? _; done.
        }
        {
          rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
          idtac.
          have K : (to_nat (U "0x007d")) = 125 by admit.
          rewrite [in X in drop_bytes _ X] K.
          compute [drop_bytes minus string_half_len].
          progress run.
          have -> : (to_nat (U "0x00ad")) = 173 by admit.
          compute [drop_bytes minus string_half_len].
          rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
          progress run.
          set b3 := is_zero _.
          case_eq b3 => b3_eq; run.
          {
            set b4 := is_zero _.
            case_eq b4 => b4_eq; run.
            {
              set b5 := is_zero _.
              case_eq b5 => b5_eq.
              {
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                run.
                have -> : (to_nat (U "0x013b")) = 315 by admit.
                compute [drop_bytes string_half_len minus].

                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                run.
                have -> : (to_nat (U "0x008e")) = 142 by admit.
                compute [drop_bytes string_half_len minus].
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
                have -> : (to_nat (U "0x0131")) = 305 by admit.
                compute [drop_bytes string_half_len minus].
                run.
                idtac.
                have -> : (to_nat (U "0x013b")) = 315 by admit.
                compute [drop_bytes string_half_len minus].
                run.
                have -> : (to_nat (U "0x008e")) = 142 by admit.
                compute [drop_bytes string_half_len minus].
                (* pushn 40, mload, dup1, dup3, dup2 *)

                run.
                rewrite/interesting/str.

                case => ? _.
                done.
              }
            }
            {
              have -> : (to_nat (U "0x0119")) = 281 by admit.
              compute [drop_bytes string_half_len minus].
              run.
              rewrite-/b4.
              rewrite b4_eq.
              run.
              have -> : (to_nat (U "0x0131")) = 305 by admit.
              compute [drop_bytes string_half_len minus];
              run.
              idtac.
              have -> : (to_nat (U "0x013b")) = 315 by admit.
              compute [drop_bytes string_half_len minus];
              run.
              have -> : (to_nat (U "0x008e")) = 142 by admit.
              compute [drop_bytes string_half_len minus];
              run.

              rewrite/interesting/str.
              by case => ? _.
            }
          }
          {
            run.
            idtac.

            have -> : (to_nat (U "0x013a"))= 314 by admit.
            compute [drop_bytes string_half_len minus];
            run.
            idtac.
            have -> : (to_nat (U "0x008e")) = 142 by admit.
            compute [drop_bytes string_half_len minus];
            run.
            rewrite/interesting/str.
            by move => [? _].
          }
        }
      }
      {
        have -> : (to_nat (U "0x0070")) = 112 by admit.
        compute [drop_bytes string_half_len minus];
        run.
        have -> : (to_nat (U "0x0140")) = 320 by admit.
        compute [drop_bytes string_half_len minus];
        run.
        set b7 := is_zero _.
        case_eq b7 => b7_eq.
        {
          run.
          idtac.
          set b8 := is_zero _.
          case_eq b8 => b8_eq.
          {
            run.

            idtac.
            have -> : (U "0x00") = zero by admit.
            have -> : forall x, (exp x zero) = one by admit.
            have -> : forall y, (div y one)  = y   by admit.
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
            idtac.
            have -> : (to_nat (U "0x01de")) = 478 by admit.
            compute [drop_bytes string_half_len minus];
              run.
            idtac.
            have -> : (to_nat (U "0x007b")) = 123 by admit.
            compute [drop_bytes string_half_len minus];
              run.

            rewrite/interesting/str.
            case => ? _; done.
          }
        }
        {
          have -> : (to_nat (U "0x01df")) = 479 by admit.
            compute [drop_bytes string_half_len minus];
              run.
          idtac.
            have -> : (to_nat (U "0x007b")) = 123 by admit.
            compute [drop_bytes string_half_len minus];
              run.

            idtac.
            rewrite/interesting/str.
            case => ? _; done.
        }
      }
    }
    {
      rewrite tn.
      compute [drop_bytes string_half_len minus];
        run.
      rewrite hg.
      compute [drop_bytes string_half_len minus];
        run.
      idtac.
      rewrite gg.
      compute [drop_bytes string_half_len minus];
        run.
      rewrite/interesting/str.
      case => ? _; done.
    }
  Qed.


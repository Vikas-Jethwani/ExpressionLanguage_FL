use "signatureFLX0.sml";

structure Flx : FLX =
struct
    datatype term = VAR of string   (* variable *)
                  | Z               (* zero *)
                  | T               (* true *)
                  | F               (* false *)
                  | P of term       (* Predecessor *)
                  | S of term       (* Successor *)
                  | ITE of term * term * term   (* If then else *)
                  | IZ of term      (* is zero *)
                  | GTZ of term     (* is greater than zero *)

    exception Not_wellformed
    exception Not_nf
    exception Not_int

    fun fromInt 0 = Z
      | fromInt curr =
            if curr > 0 then S (fromInt(curr-1))
            else P (fromInt(curr+1))

    fun toInt Term =
        let
            (* fun toInt_wr(Term, sign, curr) *)
            fun toInt_wr(Z, _, curr) = curr
              | toInt_wr(P t, 1, _) = raise Not_nf
              | toInt_wr(S t, ~1, _) = raise Not_nf
              | toInt_wr(P t, _, curr) = toInt_wr(t, ~1, curr-1)
              | toInt_wr(S t, _, curr) = toInt_wr(t, 1, curr+1)
              | toInt_wr(_, _, _) = raise Not_int
        in
            toInt_wr(Term, 0, 0)
        end;

    (* ERROR *)
    fun toString Term = 
        let
            fun toString_wr(Z, L_terms) = List.rev("Z"::L_terms)
              | toString_wr(T, L_terms) = List.rev("T"::L_terms)
              | toString_wr(F, L_terms) = List.rev("F"::L_terms)
              | toString_wr(P t, L_terms) = toString_wr(t, "(P "::L_terms)
              | toString_wr(S t, L_terms) = toString_wr(t, "(S "::L_terms)
              
        in
            String.concat( toString_wr( Term, [] ) )
        end;
    



end; (* struct *)
open Flx;
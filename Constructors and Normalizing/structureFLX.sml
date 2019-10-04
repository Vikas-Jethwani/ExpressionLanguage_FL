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

    fun toString Term = 
        let
            fun toString_wr(VAR(x)) = x
              | toString_wr(Z) = "Z"
              | toString_wr(T) = "T"
              | toString_wr(F) = "F"
              | toString_wr(P t) = "(P " ^ toString_wr(t) ^ ")"
              | toString_wr(S t) = "(S " ^ toString_wr(t) ^ ")"
              | toString_wr(IZ t) = "(IZ " ^ toString_wr(t) ^ ")"
              | toString_wr(GTZ t) = "(GTZ " ^ toString_wr(t) ^ ")"
              | toString_wr(ITE(t, t1, t0)) = "(ITE <" ^ toString_wr(t) ^ "," ^ toString_wr(t1) ^ "," ^ toString_wr(t0) ^ ">)"
              
        in
            toString_wr(Term)
        end;

    fun getFirstToken(Z) = "Z"
      | getFirstToken(T) = "T"
      | getFirstToken(F) = "F"
      | getFirstToken(P( t )) = "P"
      | getFirstToken(S( t )) = "S"
      | getFirstToken(IZ( t )) = "IZ"
      | getFirstToken(GTZ( t )) = "GTZ"
      | getFirstToken(ITE(t, t1, t0)) = "ITE"
      
    fun getRestToken(P( t )) = t
      | getRestToken(S( t )) = t
      
    fun checkConsistency(Z, _) = true
      | checkConsistency(P( t ), "P") = checkConsistency(t, "P")
      | checkConsistency(S( t ), "S") = checkConsistency(t, "S")
      | checkConsistency(_, _) = false

    fun normalize Term =
        let
            fun normalize_wr(Z) = Z
              | normalize_wr(T) = T
              | normalize_wr(F) = F
              | normalize_wr(S( t )) =
                    let
                        val norm = normalize_wr(t)
                        val tok = getFirstToken(norm)
                        val usless = (print(toString(norm));print(" <- S end\n");5)
                    in
                        if tok = "P" then getRestToken(norm)
                        else S(norm)
                    end
              | normalize_wr(P( t )) =
                    let
                        val norm = normalize_wr(t)
                        val tok = getFirstToken(norm)
                        val usless = (print(toString(norm));print(" <- P end\n");5)
                    in
                        if tok = "S" then getRestToken(norm)
                        else P(norm)
                    end
              | normalize_wr(IZ( t )) = 
                    let
                        val norm = normalize_wr(t)
                        val tok = getFirstToken(norm)
                        val usless = (print(toString(norm));print(" <- IZ end\n");5)
                    in
                        if tok = "Z" then T
                        else if tok = "P" andalso checkConsistency(norm, "P") then F
                        else if tok = "S" andalso checkConsistency(norm, "S") then F
                        else IZ(norm)
                    end
              | normalize_wr(GTZ( t )) = 
                let
                    val norm = normalize_wr(t)
                    val tok = getFirstToken(norm)
                    val usless = (print(toString(norm));print(" <- GTZ end\n");5)
                in
                    if tok = "Z" then F
                    else if tok = "P" andalso checkConsistency(norm, "P") then F
                    else if tok = "S" andalso checkConsistency(norm, "S") then T
                    else GTZ(norm)
                end;
        in
            normalize_wr(Term)
        end;


end; (* struct *)
open Flx;
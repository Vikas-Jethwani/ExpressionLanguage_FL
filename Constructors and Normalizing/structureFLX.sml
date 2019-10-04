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

    fun getFirstToken(Z) = "Z"
      | getFirstToken(T) = "T"
      | getFirstToken(F) = "F"
      | getFirstToken(P( t )) = "P"
      | getFirstToken(S( t )) = "S"
      | getFirstToken(IZ( t )) = "IZ"
      | getFirstToken(GTZ( t )) = "GTZ"
      | getFirstToken(ITE(t, t1, t0)) = "ITE"

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
    
    fun normalize Term =
        let
            fun normalize_wr(Z) = (Z, 0)
              | normalize_wr(T) = (T, 0)
              | normalize_wr(F) = (F, 0)
              | normalize_wr(S( P( t ) )) = (#1(normalize_wr(t)), 1)   
              | normalize_wr(P( S( t ) )) = (#1(normalize_wr(t)), 1)
              | normalize_wr(S( t )) =
                    let
                        val (norm, isUpd) = normalize_wr(t)
                        val usless = (print(toString(norm));print(" <- S end\n");5)
                    in
                        if isUpd = 0 then (S(norm), 0)
                        else normalize_wr(S(norm))
                    end
              | normalize_wr(P( t )) =
                    let
                        val (norm, isUpd) = normalize_wr(t)
                        val usless = (print(toString(norm));print(" <- P end\n");5)
                    in
                        if isUpd = 0 then (P(norm), 0)
                        else normalize_wr(P(norm))
                    end
              | normalize_wr(IZ( t )) = 
                    let
                        val (norm, isUpd) = normalize_wr(t)
                        val usless = (print(toString(norm));print(" <- IZ end\n");5)
                    in
                        if isUpd = 0 then
                            if norm = Z then (T, 1)
                            else (F, 1) (* Handle case of not T/F *)
                        else normalize_wr(IZ(norm))
                    end
              | normalize_wr(GTZ( t )) = 
                let
                    val (norm, isUpd) = normalize_wr(t)
                    val usless = (print(toString(norm));print(" <- GTZ end\n");5)
                in
                    if isUpd = 0 then
                        if norm = Z then (F, 1)
                        else (T, 1)
                    else normalize_wr(GTZ(norm))
                end;
                (* Wrong at normalize(GTZ(P(P(S(S(P Z)))))); *)
            val (sol, _) = normalize_wr(Term)      
        in
            sol
        end;


end; (* struct *)
open Flx;
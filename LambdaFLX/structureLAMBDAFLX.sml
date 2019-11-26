 use "signatureLAMBDAFLX.sml" ;

structure LambdaFlx : LAMBDAFLX =
struct
    datatype lterm = term (* term from FLX *)
                   | VAR of string      (* variables *)
                   | Z                  (* zero *)
                   | T                  (* true *)
                   | F                  (* false *)
                   | P of lterm         (* Predecessor *)
                   | S of lterm         (* Successor *)
                   | IZ of lterm        (* is zero *)
                   | GTZ of lterm       (* is greater than zero *)
                   | ITE of lterm * lterm * lterm       (* If then else *)
                   | LAMBDA of lterm * lterm    (* lambda x [lterm] *)
                   | APP of lterm * lterm       (* application of lambda terms, i.e. (L M) *)
                                        
    exception Not_wellformed
    exception Not_nf
    exception Not_int
    exception Not_welltyped

(*
    fun isWellFormed(VAR x) = true
      | isWellFormed(Z) = true
      | isWellFormed(T) = true
      | isWellFormed(F) = true
      | isWellFormed(P t) = isWellFormed(t)
      | isWellFormed(S t) = isWellFormed(t)
      | isWellFormed(IZ t) = isWellFormed(t)
      | isWellFormed(GTZ t) = isWellFormed(t)
      | isWellFormed( ITE(t0, t1, t2) ) = isWellFormed(t0) andalso isWellFormed(t1) andalso isWellFormed(t2)
      | isWellFormed( APP(t0, t1) ) = isWellFormed(t0) andalso isWellFormed(t1)
      | isWellFormed( LAMBDA(VAR x, t1) ) = isWellFormed(t1)
      | isWellFormed( LAMBDA(_, _) ) = false
*)
    
    
    
    fun fromInt 0 = Z
      | fromInt curr =
            if curr > 0 then S (fromInt(curr-1))
            else P (fromInt(curr+1)) ;

    fun toInt LTerm =
            let
                fun which_err(Z) = raise Not_nf
                  | which_err(P t) = which_err(t)
                  | which_err(S t) = which_err(t)
                  | which_err(_) = raise Not_int ;

                (* fun toInt_wr(Term, sign, curr) *)
                fun toInt_wr(Z, _, curr) = curr
                  | toInt_wr(P t, 1, _) = which_err(t)
                  | toInt_wr(S t, ~1, _) = which_err(t)
                  | toInt_wr(P t, _, curr) = toInt_wr(t, ~1, curr-1)
                  | toInt_wr(S t, _, curr) = toInt_wr(t, 1, curr+1)
                  | toInt_wr(_, _, _) = raise Not_int ;
            in
                toInt_wr(LTerm, 0, 0)
            end ;


        fun normalizeL Term =
            let
                exception Not_normalizable ;

                fun checkConsistency(Z, _) = true
                  | checkConsistency(P( t ), "P") = checkConsistency(t, "P")
                  | checkConsistency(S( t ), "S") = checkConsistency(t, "S")
                  | checkConsistency(_, _) = false ;

                fun normalize_wr(Z) = Z
                  | normalize_wr(T) = T
                  | normalize_wr(F) = F
                  | normalize_wr(P( t )) =
                        let
                            val norm = normalize_wr(t)
                        in
                            ( case norm of
                                S term' => term'
                              | _       => P(norm)
                            )
                        end
                  | normalize_wr(S( t )) =
                        let
                            val norm = normalize_wr(t)
                        in
                            ( case norm of
                                P term' => term'
                              | _       => S(norm)
                            )
                        end
                  | normalize_wr(IZ( t )) = 
                        let
                            val norm = normalize_wr(t)
                        in
                            ( case norm of
                                Z       => T
                              | P term' => if checkConsistency(norm, "P") then F
                                           else IZ(norm)
                              | S term' => if checkConsistency(norm, "S") then F
                                           else IZ(norm)
                              | _       => IZ(norm)
                            )
                        end
                  | normalize_wr(GTZ( t )) = 
                    let
                        val norm = normalize_wr(t)
                    in
                        ( case norm of
                            Z       => F
                          | P term' => if checkConsistency(norm, "P") then F
                                       else GTZ(norm)
                          | S term' => if checkConsistency(norm, "S") then T
                                       else GTZ(norm)
                          | _       => GTZ(norm)
                        )
                    end
                  | normalize_wr(ITE( t0,t1,t2 )) = 
                        let
                            val norm0 = normalize_wr(t0)
                            val norm1 = normalize_wr(t1)
                            val norm2 = normalize_wr(t2)
                        in
                            ( case norm0 of
                                T       => norm1
                              | F       => norm2
                              | GTZ term'       =>  if norm1=norm2 then norm1
                                                    else ITE(norm0, norm1, norm2)
                              | IZ term'        =>  if norm1=norm2 then norm1
                                                    else ITE(norm0, norm1, norm2)
                            )
                        end
                  | normalize_wr(VAR t) = VAR t
                  | normalize_wr(APP( t0,t1 )) =
                        let
                            val norm0 = normalize_wr(t0)
                            val norm1 = normalize_wr(t1)
                        in
                              APP(norm0, norm1)
                        end
                  | normalize_wr(LAMBDA( t0,t1 )) =
                        let
                            val norm0 = normalize_wr(t0)
                            val norm1 = normalize_wr(t1)
                        in
                              LAMBDA(norm0, norm1)
                        end
            in
                normalize_wr(Term)
            end ;




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
                  | toString_wr(ITE(t0, t1, t2)) = "(ITE <" ^ toString_wr(t0) ^ "," ^ toString_wr(t1) ^ "," ^ toString_wr(t2) ^ ">)"
                  | toString_wr(LAMBDA(t0, t1)) = "LAMBDA " ^ toString_wr(t0) ^ "[" ^ toString_wr(t1) ^ "]"
                  | toString_wr(APP(t0, t1)) = "(" ^ toString_wr(t0) ^ " " ^ toString_wr(t1) ^ ")"
            in
                toString_wr(Term)
            end ;
            
    fun fromString str = 
            let
                fun find_terms([], [], [t], _) = t
                  | find_terms(#" "::left, tokens, terms, " ") = raise Not_wellformed
                  | find_terms(#" "::left, "(APP"::tokens, terms, _) = find_terms(left, "(APP"::tokens, terms, " ") (* Space between application *)
                  | find_terms(#"Z"::left, tokens, terms, _) = find_terms(left, tokens, (Z::terms), "Z")
                  | find_terms(#"T"::left, tokens, terms, _) = find_terms(left, tokens, (T::terms), "T")
                  | find_terms(#"F"::left, tokens, terms, _) = find_terms(left, tokens, (F::terms), "F")

                  | find_terms(#"(" :: #"P" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(P")::tokens, terms, " ")
                  | find_terms(#"(" :: #"S" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(S")::tokens, terms, " ")
                  | find_terms(#"(" :: #"I" :: #"Z" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(IZ")::tokens, terms, " ")
                  | find_terms(#"(" :: #"G" :: #"T" :: #"Z" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(GTZ")::tokens, terms, " ")
                  | find_terms(#"(" :: #"I" :: #"T" :: #"E" :: #" " :: #"<" :: left, tokens, terms, _) = find_terms(left, ("(ITE")::tokens, terms, "<")
                  | find_terms(#"L" :: #"A" :: #"M" :: #"B" :: #"D" :: #"A" :: #" " :: left, tokens, terms, _) = find_terms(left, ("(L1")::tokens, terms, " ")
                  | find_terms(#"[" :: left, tokens, (VAR x)::terms, _) = find_terms(left, ("(L2")::tokens, (VAR x)::terms, "[")
                  | find_terms(#"[" :: left, tokens, (somehting_else)::terms, _) = raise Not_wellformed  (* LAMBDA ka first term not variable *)
                  | find_terms(#"(" :: #"(" :: left, tokens, terms, _) = find_terms(#"(" ::left, ("(APP")::tokens, terms, "(")
                  | find_terms(#"(" :: #"Z" :: left, tokens, terms, _) = find_terms(#"Z" ::left, ("(APP")::tokens, terms, "Z")
                  | find_terms(#"(" :: #"T" :: left, tokens, terms, _) = find_terms(#"T" ::left, ("(APP")::tokens, terms, "T")
                  | find_terms(#"(" :: #"F" :: left, tokens, terms, _) = find_terms(#"F" ::left, ("(APP")::tokens, terms, "F")
                  | find_terms(#"(" :: #"L" :: left, tokens, terms, _) = find_terms(#"L" ::left, ("(APP")::tokens, terms, "L")
                  | find_terms(#"(" :: c :: left, tokens, terms, _) = 
                            if Char.isLower(c) then find_terms( c::left, ("(APP")::tokens, terms, "")
                            else raise Not_wellformed

                  | find_terms(#")"::left, "(P"::tokens, t::terms, _) = find_terms(left, tokens, (P t)::terms, "P")
                  | find_terms(#")"::left, "(S"::tokens, t::terms, _) = find_terms(left, tokens, (S t)::terms, "S")
                  | find_terms(#")"::left, "(IZ"::tokens, t::terms, _) = find_terms(left, tokens, (IZ t)::terms, "IZ")
                  | find_terms(#")"::left, "(GTZ"::tokens, t::terms, _) = find_terms(left, tokens, (GTZ t)::terms, "GTZ")
                  | find_terms(#")"::left, "(APP"::tokens, t0::t1::terms, _) = find_terms(left, tokens, (APP(t1,t0))::terms, "APP")

                  | find_terms(#","::left, tokens, terms, ",") = raise Not_wellformed
                  | find_terms(#","::left, tokens, terms, _) = find_terms(left, tokens, terms, ",")
                  | find_terms(#">" :: #")"::left, "(ITE"::tokens, t0::t1::t2::terms, _) = find_terms(left, tokens, (ITE(t2,t1,t0))::terms, ">")
                  | find_terms(#"]"::left, "(L2"::"(L1"::tokens, t0::t1::terms, _) = find_terms(left, tokens, (LAMBDA(t1,t0))::terms, "]")
                  | find_terms(c::left, tokens, (VAR t)::terms, "v") =
                            if Char.isLower(c) then find_terms(left, tokens, (VAR (t^Char.toString(c)))::terms, "v")
                            else raise Not_wellformed
                  | find_terms(c::left, tokens, terms, _) =
                            if Char.isLower(c) then find_terms(left, tokens, (VAR (Char.toString(c)))::terms, "v")
                            else raise Not_wellformed
                  | find_terms(_, _, _, _) = raise Not_wellformed ;

                val terms = find_terms(explode str, [], [], "")
            in
                 if (toString(terms))=str then terms
                 else raise Not_wellformed
            end ;


                fun replace_term(L, v, M)=
                    let
                        fun replace_wr(VAR x, VAR v, _) = 
                                if x=v then M
                                else VAR x
                          | replace_wr(Z, _, _) = Z
                          | replace_wr(T, _, _) = T
                          | replace_wr(F, _, _) = F
                          | replace_wr(P t, v, M) = P( replace_wr(t, v, M) )
                          | replace_wr(S t, v, M) = S( replace_wr(t, v, M) )
                          | replace_wr(IZ t, v, M) = IZ( replace_wr(t, v, M) )
                          | replace_wr(GTZ t, v, M) = GTZ( replace_wr(t, v, M) )
                          | replace_wr(ITE(t0, t1, t2), v, M) = ITE( replace_wr(t0, v, M), replace_wr(t1, v, M), replace_wr(t2, v, M) )
                          | replace_wr(LAMBDA(x, t), v, M) = LAMBDA( x, replace_wr(t, v, M) )
                          | replace_wr(APP(t0, t1), v, M) = APP( replace_wr(t0, v, M), replace_wr(t1, v, M) )
                    in
                        replace_wr(L, v, M)
                    end


                fun is_Present(x, []) = (x^"1", [(x,1)])
                  | is_Present(x, (y, count)::taill) =
                        if x=y then (x^(Int.toString(count+1)), (y, count+1)::taill)
                        else
                            let val (v,c) = is_Present(x, taill) in (v, (y, count)::c) end

                fun preprocess(VAR x, unique) = (VAR x, unique)
                  | preprocess(Z, unique) = (Z, unique)
                  | preprocess(T, unique) = (T, unique)
                  | preprocess(F, unique) = (F, unique)
                  | preprocess(P t, unique) = 
                        let
                            val (Term, uniq) = preprocess(t, unique)
                        in (P(Term), uniq) end
                  | preprocess(S t, unique) = 
                        let
                            val (Term, uniq) = preprocess(t, unique)
                        in (S(Term), uniq) end
                  | preprocess(IZ t, unique) = 
                        let
                            val (Term, uniq) = preprocess(t, unique)
                        in (IZ(Term), uniq) end
                  | preprocess(GTZ t, unique) = 
                        let
                            val (Term, uniq) = preprocess(t, unique)
                        in (GTZ(Term), uniq) end
                  | preprocess(ITE(t0, t1, t2), unique) = 
                        let
                            val (Term0, uniq0) = preprocess(t0, unique)
                            val (Term1, uniq1) = preprocess(t1, uniq0)
                            val (Term2, uniq2) = preprocess(t2, uniq1)
                        in (ITE(Term0, Term1, Term2), uniq2) end
                  | preprocess(APP(t0, t1), unique) = 
                        let
                            val (Term0, uniq0) = preprocess(t0, unique)
                            val (Term1, uniq1) = preprocess(t1, uniq0)
                        in (APP(Term0, Term1), uniq1) end
                  | preprocess(LAMBDA(VAR x, t), unique) = 
                        let
                            val (v, uniq) = is_Present(x, unique)
                            val half_processed = replace_term(t, VAR x, VAR v)
                            val (Term, uniq1) = preprocess(half_processed, uniq)
                        in (LAMBDA(VAR v, Term), uniq1) end



        
        
        (* 0=BOOL; 1=INT; ~1=NOT_DEFINED_YET *)
    fun isWellTyped LTerm =
             let
                     (* var, table, what_to_do *)
                 fun lookup_ins_upd(VAR x, [], what) = (what, [(x,what)]) (* Insert *)
                   | lookup_ins_upd(VAR x, ((y, typ)::sym_tab), what) = 
                         if x=y andalso what= ~1 then (typ, ((y, typ)::sym_tab) ) (* lookup *)
                         else if x=y andalso typ= ~1 then (what, ((y, what)::sym_tab) ) (* update from not_defined *)
                         else if x=y andalso typ=what then (what, ((y, typ)::sym_tab) ) (* update with same *)
                         else if x=y andalso typ<>what then (~2, ((y, typ)::sym_tab) ) (* EXCEPTION ~2 *)
                         else
                             let val (typ0, sym_tab0) = lookup_ins_upd(VAR x, sym_tab, what)
                             in ( typ0, ((y, typ)::sym_tab0) ) end
                  (*| lookup_ins_upd(Test_Term,tab,what) = (print(toString(Test_Term));(~1,tab)) *)


           

                     (* Term, Symbol_Table, Constraints *) (* true/false, return_type, symbol_table, constraints, return_term *) 
                 fun isWellTyped_wr(VAR x, sym_tab, cons) =
                        let val (typ, sym_tab0) = lookup_ins_upd(VAR x, sym_tab, ~1)
                        in (true, typ, sym_tab0, cons, VAR x) end (* check if VAR x or x *)
                        
                   | isWellTyped_wr(Z, sym_tab, cons) = (true, 1, sym_tab, cons, Z)
                   | isWellTyped_wr(T, sym_tab, cons) = (true, 0, sym_tab, cons, T)
                   | isWellTyped_wr(F, sym_tab, cons) = (true, 0, sym_tab, cons, F)
                   
                   | isWellTyped_wr(P t, sym_tab, cons) =
                         let
                             val (t_f, typ, sym_tab0, cons0, ret_term) = isWellTyped_wr(t, sym_tab, cons)
                             val (typ1, sym_tab1) = if typ = ~1 then lookup_ins_upd(t, sym_tab0, 1)
                                                    else (1, sym_tab0)
                         in
                             if typ<>0 andalso typ <> ~2 andalso typ1 <> ~2 then (t_f, 1, sym_tab1, cons0, ret_term)
                             else (false, 1, sym_tab1, cons0, ret_term)
                         end
                         
                   | isWellTyped_wr(S t, sym_tab, cons) =
                         let
                             val (t_f, typ, sym_tab0, cons0, ret_term) = isWellTyped_wr(t, sym_tab, cons)
                             val (typ1, sym_tab1) = if typ = ~1 then lookup_ins_upd(t, sym_tab0, 1)
                                                    else (1, sym_tab0)
                         in
                             if typ<>0 andalso typ1 <> ~2 then (t_f, 1, sym_tab1, cons0, ret_term)
                             else (false, 1, sym_tab1, cons0, ret_term)
                         end
                         
                   | isWellTyped_wr(IZ t, sym_tab, cons) =
                         let
                             val (t_f, typ, sym_tab0, cons0, ret_term) = isWellTyped_wr(t, sym_tab, cons)
                             val (typ1, sym_tab1) = if typ = ~1 then lookup_ins_upd(t, sym_tab0, 1)
                                                    else (1, sym_tab0)
                         in
                             if typ<>0 andalso typ1 <> ~2 then (t_f, 0, sym_tab1, cons0, ret_term)
                             else (false, 0, sym_tab1, cons0, ret_term)
                         end
                         
                   | isWellTyped_wr(GTZ t, sym_tab, cons) =
                         let
                             val (t_f, typ, sym_tab0, cons0, ret_term) = isWellTyped_wr(t, sym_tab, cons)
                             val (typ1, sym_tab1) = if typ = ~1 then lookup_ins_upd(t, sym_tab0, 1)
                                                    else (1, sym_tab0)
                         in
                             if typ<>0 andalso typ1 <> ~2 then (t_f, 0, sym_tab1, cons0, ret_term)
                             else (false, 0, sym_tab1, cons0, ret_term)
                         end
                         
                   | isWellTyped_wr(ITE(t0, t1, t2), sym_tab, cons) =
                         let
                            val (t_f0, typ0, sym_tab0, cons0, ret_term0) = isWellTyped_wr(t0, sym_tab, cons)
                            val (t_f1, typ1, sym_tab1, cons1, ret_term1) = isWellTyped_wr(t1, sym_tab0, cons0)
                            val (t_f2, typ2, sym_tab2, cons2, ret_term2) = isWellTyped_wr(t2, sym_tab1, cons1)
                             
                             
                            
                            
                            val (typ3, sym_tab3) = if typ0 = ~1 then lookup_ins_upd(ret_term0, sym_tab2, 0)
                                                   else (typ0, sym_tab2)
                            
                            val (typ4, typ5, sym_tab4, cons3) = 
                                if typ1= ~1 andalso typ2<> ~1 andalso typ2<> ~2 then
                                    let
                                        val (new_typ1, new_sym_tab3) = lookup_ins_upd(ret_term1, sym_tab3, typ2)
                                    in
                                        (new_typ1, typ2, new_sym_tab3, cons2)
                                    end
                                else if typ1<> ~1 andalso typ1<> ~2 andalso typ2= ~1 then
                                    let
                                        val (new_typ2, new_sym_tab3) = lookup_ins_upd(ret_term2, sym_tab3, typ1)
                                    in
                                        (typ1, new_typ2, new_sym_tab3, cons2)
                                    end
                                else if typ1= ~1 andalso typ2= ~1 then
                                    (typ1, typ2, sym_tab3, (t1,t2)::(t2,t1)::cons2)  (*Add reverse too*)
                                else
                                    (typ1, typ2, sym_tab3, cons2)
                            
                         in
                            if typ3=0 andalso t_f0=true andalso t_f1=true andalso t_f2=true andalso typ4=typ5 andalso typ4=0 then (true, 0, sym_tab4, cons3, ret_term1)
                            else if typ3=0 andalso t_f0=true andalso t_f1=true andalso t_f2=true andalso typ4=typ5 andalso typ4=1 then (true, 1, sym_tab4, cons3, ret_term1)
                            else if typ3=0 andalso t_f0=true andalso t_f1=true andalso t_f2=true andalso typ4=typ5 andalso typ4= ~1 then (true, ~1, sym_tab4, cons3, ret_term1)
                            else (false, typ5, sym_tab4, cons3, ret_term1)
                         end
                         
                   | isWellTyped_wr(LAMBDA(t0, t1), sym_tab, cons) =
                        let
                            val (t_f, typ, sym_tab0, cons0, ret_term) = isWellTyped_wr(t1, sym_tab, cons)
                            val (typ1, sym_tab1) = if typ = ~1 then lookup_ins_upd(t1, sym_tab0, ~1)
                                                   else (typ, sym_tab0)
                        in
                            if typ <> ~2 andalso typ1 <> ~2 then (t_f, typ1, sym_tab1, cons0, ret_term) (*return type of lambda term not decided *)
                            else (false, typ1, sym_tab1, cons0, ret_term)
                        end

                   | isWellTyped_wr(APP(LAMBDA(t0, t1), t2), sym_tab, cons) =
                        let
                            val (t_f0, typ0, sym_tab0, cons0, ret_term0) = isWellTyped_wr(LAMBDA(t0, t1), sym_tab, cons)
                            val (t_f1, typ1, sym_tab1, cons1, ret_term1) = isWellTyped_wr(t2, sym_tab0, cons0)
                            (*val beta_nf_ke_baad = betanf(APP(LAMBDA(t0, t1), t2))*)
                            (*val isWT = #1(isWellTyped_wr(beta_nf_ke_baad, [], []))*)
                            
                        in
                            if typ0 <> ~2 andalso typ1 <> ~2 andalso t_f0=true then (t_f1, typ1, sym_tab1, cons1, ret_term1) (*return type of lambda term not decided *)
                            else (false, typ1, sym_tab1, cons1, ret_term1)
                        end
                   | isWellTyped_wr(APP(APP(t0, t1), t2), sym_tab, cons) =
                        let
                            val (t_f0, typ0, sym_tab0, cons0, ret_term0) = isWellTyped_wr(APP(t0, t1), sym_tab, cons)
                            val (t_f1, typ1, sym_tab1, cons1, ret_term1) = isWellTyped_wr(t2, sym_tab0, cons0)
                            (*val beta_nf_ke_baad = betanf(APP(LAMBDA(t0, t1), t2))*)
                            (*val isWT = #1(isWellTyped_wr(beta_nf_ke_baad, [], []))*)
                            
                        in
                            if typ0 <> ~2 andalso typ1 <> ~2 andalso t_f0=true then (t_f1, typ1, sym_tab1, cons1, ret_term1) (*return type of lambda term not decided *)
                            else (false, typ1, sym_tab1, cons1, ret_term1)
                        end
                    | isWellTyped_wr(APP(VAR x, VAR y), sym_tab, cons) = (true, ~1, sym_tab, cons, VAR x)
                    | isWellTyped_wr(_, _, _) = (false, ~1, [], [], VAR "x")
                        

                val (a1,a2,a3,a4,a5) = isWellTyped_wr(#1(preprocess(fromString(toString(LTerm)),[])), [], [])
            in
                 a1
            end ;
                   
                   



        fun betanf LTerm =
            let
                fun betanf_wr(VAR v) = VAR v
                  | betanf_wr(Z) = Z
                  | betanf_wr(T) = T
                  | betanf_wr(F) = F
                  | betanf_wr(P t) = P(betanf_wr(t))
                  | betanf_wr(S t) = S(betanf_wr(t))
                  | betanf_wr(IZ t) = IZ(betanf_wr(t))
                  | betanf_wr(GTZ t) = GTZ(betanf_wr(t))
                  | betanf_wr(ITE(t0, t1, t2)) = ITE( betanf_wr(t0), betanf_wr(t1), betanf_wr(t2) )
                  | betanf_wr(LAMBDA(v, t)) = LAMBDA( v, betanf_wr(t) )
                  | betanf_wr(APP( LAMBDA(VAR v, L), M )) = betanf_wr(replace_term(L, VAR v, M))
                  | betanf_wr(APP( APP(x, y), M )) = betanf_wr( APP( betanf_wr(APP( x, y )), M) )


                val well_formed_wala = #1(preprocess(fromString(toString(LTerm)),[]))
                val uselss = isWellTyped(well_formed_wala)
            in
                if uselss=true then normalizeL(betanf_wr(well_formed_wala))
                else raise Not_welltyped
                
            end ;
                            
   

end ; (* struct *)
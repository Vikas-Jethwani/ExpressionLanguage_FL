use "structureFLX.sml";

open Flx;

(* Sample terms *)
val t1 = VAR "abc";
val t2 = Z;
val t3 = F;
val t4 = ITE (t3,t1,t2);
val t5 = fromInt 4;
val t6 = fromInt ~3;
val t9 = P (S Z);

val v01 = normalize(S(S(S(P(P(P Z))))));
val v02 = normalize(GTZ(P(P(S(S(P Z))))));
val v03 = normalize(IZ(S(GTZ(Z))));
val v04 = normalize(IZ(S(S(GTZ(P(P Z))))));
val v05 = normalize(ITE(GTZ Z, P Z, P(P Z)));
val v06 = P(S(P T));
val v07 = fromString("(P (S (IZ (GTZ T))))");
val v08 = fromString("(IZ (GTZ T))");
val v09 = fromString("(P (S Z))");

val v13 = "(ITE <(ITE <a,b,c,d>),e>)";
val v14 = "(ITE <T,,T,T>)";
val v15 = fromString("(GTZ (ITE <T,(ITE <T,F,abcd>),pqrs>))");
val v16 = fromString("(ITE <T,a,a>)");
val v17 = ("a(ITE <aa,ab>)");
val v18 = fromString "(ITE <(ITE <T,F,T>),(IZ (S (P Z))),(GTZ (IZ Z))>)";
val v19 = fromInt(toInt(fromString("(S (S Z))")));
val v20 = toInt(fromInt(5));
val v21 = toInt(fromInt(~5));
val v22 = toInt(fromInt(0));
val v23 = fromString(toString(ITE (ITE (T,F,T),ITE (F,F,T),ITE (F,F,F))));
val v24 = ("");

val v27 = ("(S (ITE (T,F,T)))");
val v28 = ("(S (ITE <(ITE <var abcd,T,F>),F,T>))");
val v29 = fromString("(S (ITE <(ITE <varabcd,T,F>),F,T>))");
val v30 = fromString("(ITE <(ITE <T,F,T>),(ITE <F,F,T>),(ITE <T,T,T>)>)");
val v31 = ("(ITE <(ITE <T,F,T>),(ITE <F,F,T>),(ITE <T,T,T,T>)>)");
val v32 = fromString("(IZ (ITE <T,(ITE <T,F,abcd>),pqrs>))");
val v33 = fromString("(GTZ (ITE <T,(ITE <T,F,abcd>),pqrs>))");
val v34 = "IZ ";
val v35 = "GTZ ";
val v36 = P (ITE(T, Z, Z));

(* Test cases for fromInt and toInt *)
val resultint1 = (case (toInt t5) of 
                        4 => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle _ => (print "Incorrect\n"; false);

val resultint2 = (case (toInt t6) of 
                        ~3 => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle _ => (print "Incorrect\n"; false);

val resultInt3 = (case (toInt t4) of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_int => (print "correct\n"; true)
                        handle _ => (print "Incorrect\n"; false);

val resultInt4 =  (case (toInt (S (S (Z)))) of 
                        2 => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle _ => (print "Incorrect\n"; false);


(* Test cases for fromString *)
val resultstring1 = (case (fromString "a") of 
                        (VAR "a") => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);

val resultstring2 = (case (fromString "abcd efgh") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "correct\n"; true);

val resultstring3 = (case (fromString "(ITE <F,abc,Z>)") of 
                        ITE (F, VAR("abc"), Z) => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);

val resultstring4 = (case (fromString "(S (S Z))") of 
                        S (S (Z)) => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);


(* Test cases for toString *)
(* Make sure to properly parenthesize the constructor applications and use 
angular brackets for ITE in your output string *)
(* Do not print VAR for variable names in the output string *)
val resultstring5 = (case (toString t1) of 
                        "abc" => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false));

val resultstring6 = (case (toString t2) of 
                        "Z" => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false));

val resultstring7 = (case (toString t4) of 
                        "(ITE <F,abc,Z>)" => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false));

(* Test cases for normalize *)

val resultnorm1 = (case (normalize t9) of 
                Z => (print "correct\n"; true)
                | _ => (print "incorrect\n"; false));



(* ------------------------------- My Testcases ------------------------- *)
val result01 = ( case v01 of 
                    Z => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false))
                        handle _ => (print "Incorrect\n"; false);

val result02 = ( case v02 of 
                    F => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result03 = ( case v03 of 
                    IZ (S F) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result04 = ( case v04 of 
                    IZ (S (S F)) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result05 = ( case v05 of 
                    P (P Z) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result06 = ( case toInt(v06) of 
                  _ => (print "Incorrect\n"; false)
               )handle _ => (print "correct\n"; false);
               
val result07 = ( case v07 of 
                    P (S (IZ (GTZ T))) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result08 = ( case v08 of 
                    IZ (GTZ T) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result09 = ( case v09 of 
                    P (S Z) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )


val result13 = ( case fromString(v13) of 
                    _ => (print "Incorrect\n"; false)
               )handle _ => (print "correct\n"; false);

               
val result14 = ( case fromString(v14) of 
                    _ => (print "Incorrect\n"; false)
               )handle _ => (print "correct\n"; false);

               
val result15 = ( case v15 of 
                    GTZ (ITE (T,ITE (T,F,VAR "abcd"),VAR "pqrs")) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )

               
val result16 = ( case v16 of 
                    ITE (T,VAR "a",VAR "a") => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
val result17 = ( case fromString(v17) of 
                    _ => (print "Incorrect\n"; false)
               )handle _ => (print "correct\n"; false);

               
val result18 = ( case v18 of 
                    ITE (ITE (T,F,T),IZ (S (P Z)),GTZ (IZ Z)) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )

          
val result19 = ( case v19 of 
                    S (S Z) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result20 = ( case v20 of 
                    5 => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )

               
val result21 = ( case v21 of 
                    ~5 => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result22 = ( case v22 of 
                    0 => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result23 = ( case v23 of 
                    ITE (ITE (T,F,T),ITE (F,F,T),ITE (F,F,F)) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result24 = ( case fromString(v24) of 
                  _ => (print "Incorrect\n"; false)
               )handle _ => (print "correct\n"; false);
               
       
               
val result27 = ( case fromString(v27) of 
                  _ => (print "Incorrect\n"; false)
               )handle _ => (print "correct\n"; false);
               
               
val result28 = ( case fromString(v28) of 
                  _ => (print "Incorrect\n"; false)
               )handle _ => (print "correct\n"; false);
               
               
val result29 = ( case v29 of 
                    S (ITE (ITE (VAR "varabcd",T,F),F,T)) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result30 = ( case v30 of 
                    ITE (ITE (T,F,T),ITE (F,F,T),ITE (T,T,T)) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result31 = ( case fromString(v31) of 
                  _ => (print "Incorrect\n"; false)
               )handle _ => (print "correct\n"; false);
               
val result32 = ( case v32 of 
                    IZ (ITE (T,ITE (T,F,VAR "abcd"),VAR "pqrs")) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result33 = ( case v33 of 
                    GTZ (ITE (T,ITE (T,F,VAR "abcd"),VAR "pqrs")) => (print "correct\n"; true)
                  | _ => (print "Incorrect\n"; false)
               )
               
val result34 = ( case fromString(v34) of 
                  _ => (print "Incorrect\n"; false)
               )handle _ => (print "correct\n"; false);
               
val result35 = ( case fromString(v35) of 
                  _ => (print "Incorrect\n"; false)
               )handle _ => (print "correct\n"; false);

               
val result36 = ( case toInt(v36) of 
                  _ => (print "Incorrect\n"; false)
               )handle _ => (print "correct\n"; false);
        

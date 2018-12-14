(**************************************************************************)
(*       ___	                                                          *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

(* Esercizio 0 
   ===========
   
   Compilare i seguenti campi:
   
   Nome1: ...
   Cognome1: ...
   Matricola1: ...
   Account1: ...
   
   Nome2: ...
   Cognome2: ...
   Matricola2: ...
   Account2: ...

   Prima di abbandonare la postazione:

   * consegnare con il solito comando
     ~sacerdot/logica1819/ConsegnaLogica NOMEFILE.ma
   
*)

include "logic/equality.ma".
include "logic/connectives.ma".

(* I numeri naturali, le liste di naturali e i booleani sono definiti come
   nelle esercitazioni precedenti. Definiamo anche one, two, three nel modo
   appropriato *)
inductive nat : Type ≝ O : nat | S : nat → nat.
definition one ≝ S O.
definition two ≝ S (S O).
definition three ≝ S (S (S O)).

inductive list_nat : Type ≝ Nil : list_nat | Cons : nat → list_nat → list_nat.

(* Esercizio 1
   ===========
   
   Scrivere laa funzione `inslast n l` che aggiunge il numero `n` in coda a `l` *)
let rec inslast n l on l ≝
 …

theorem test1:
 inslast three (Cons one (Cons two Nil)) = Cons one (Cons two (Cons three Nil)).
 done.
qed. 

(* Esercizio 2
   ===========
   
   Scrivere la funzione `reflect l` che data la lista di numeri
   n1 ... nk restituisce la lista palindroma
   n1 ... nk nk ... n1 *)
let rec reflect l on l ≝
 …
 
theorem test2:
 reflect (Cons one (Cons two (Cons three Nil))) =
  Cons one (Cons two (Cons three (Cons three (Cons two (Cons one Nil))))).
 done. 
qed.

(* Esercizio 3
   ===========
   
   Scrivere la funzione `rev` che data la lista di numeri `l` restituisce
   la stessa lista scritta al contrario *)
let rec rev l on l ≝
 …

theorem test3:
 rev (Cons one (Cons two Nil)) = Cons two (Cons one Nil).
 done.
qed.

(* Esercizio 4
   ===========
   
   Dimostrare il seguente teorema dopo aver capito l'enunciato. *)
theorem rev_inslast: ∀n,l. rev (inslast n l) = Cons n (rev l).
 assume n: nat.
 assume l: list_nat.
 we proceed by induction on l to prove ….
 case Nil.
  …
 case Cons (h: nat) (t: list_nat).
  by induction hypothesis we know … (IH).
  we need to prove …
  or equivalently ….
  (* I seguenti comandi vengono utilizzati per dimostrare E1 = Ek attraverso
     una serie di passi intermedi E1 = E2 = ... = Ek.
     Se il passo non comporta semplicemente una semplificazione usando le
     definizioni è possibile usare `by teoremi` per giustificarlo. *)
  conclude
     (inslast h (rev (inslast n t)))
   = (inslast h (Cons n (rev t))) by IH.
   = (Cons n (inslast h (rev t)))
 done.
qed.

(* La prossima linea definisce `palindrome l` come `l = rev l`.
   In particolare, la sintassi `λx.M` si usa per una funzione anonima
   il cui input è il parametro formale `x` e il cui output è il termine `M`
   che ovviamente può usare `x`. *)
definition palindrome ≝ λl. l = rev l.

(* Esercizio 5
   ===========
   
   Dimostrare che la reflect di una stringa è palindroma.

   Suggerimento: nel caso Cons è necessario usare una lunga catena
   di equazioni. Nella catena è necessario usare il lemma rev_inslast.   
*)
theorem palindrome_reflect: ∀l. palindrome (reflect l).
 …
qed.

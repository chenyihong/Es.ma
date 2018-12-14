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



(* ATTENZIONE
   ==========

   Quanto segue sono definizioni di tipi di dato/grammatiche e funzioni
   definite per ricorsione strutturale prese dall'esercitazione della volta
   scorsa. Non cambiarle e procedere con i nuovi esercizi di dimostrazione
   che sono intervallati con le definizioni.
*)

include "logic/equality.ma".
include "logic/connectives.ma".

(* Definiamo una notazione per `iff` *)
notation "hvbox(A break ⇔ B)" left associative with precedence 30 for
@{'iff $A $B}.
interpretation "iff" 'iff A B = (iff A B).

(* nat ::= "O" | "S" nat   *)
inductive nat : Type ≝
   O : nat
 | S : nat → nat.

definition one ≝ S O.
definition two ≝ S (S O).
definition three ≝ S (S (S O)).

(* list_nat ::= "Nil" | "Cons" nat list_nat *)
inductive list_nat : Type ≝
   Nil : list_nat
 | Cons : nat → list_nat → list_nat.

(* bool ::= "true" | "false" *)
inductive bool : Type ≝
 | true : bool
 | false : bool.

(* `bool_and` implementa l'operatore && sui booleani *)
let rec bool_and x y on x ≝
 match x with
 [ true ⇒ y
 | false ⇒ false
 ].

(* Definiamo la sintassi per il construtto `if ... then ... else ...` *)
let rec if_then_else (A:Type[0]) b (x:A) (y:A) on b ≝
 match b with
 [ true ⇒ x
 | false ⇒ y ].
notation "hvbox('if' A break 'then' B break 'else' C)" non associative
 with precedence 30 for @{if_then_else ? $A $B $C}.

(* `len n m` e' `true` se e solo se `n` e' minore o uguale di `m` *)
let rec len n m on n ≝
 match n with
 [ O ⇒ true
 | S n ⇒ match m with [ O ⇒ false | S m ⇒ len n m ]
 ].

(* `eqn n m` e' `true` se e solo se `n` e' uguale a `m' *)
let rec eqn n m on n ≝ bool_and (len n m) (len m n).

(* `insert n l` inserisce `n` nella lista ordinata `l`, in modo
    da ottenere ancora una lista ordinata *)
let rec insert n l on l ≝
 match l with
 [ Nil ⇒ Cons n Nil
 | Cons n' l' ⇒ if len n n' then Cons n l else Cons n' (insert n l')
 ].

(* `insertion_sort l` ordina la lista `l` usando l'algoritmo
    di insertion sort *)
let rec insertion_sort l on l ≝
 match l with
 [ Nil ⇒ Nil
 | Cons n l' ⇒ insert n (insertion_sort l')
 ].

(**********************************************************************)
(***************** LAB 19 Novembre 2018 *******************************)
(*
    Nella scorsa esercitazione, abbiamo definito una funzione `insert`
    per aggiungere un elemento in una lista ordinata, che abbiamo usato
    per scrivere la funzione `insertion_sort` che ordina una lista.
    Tale codice è stato riportato in questo file, prima di questo commento.
    
    In questa esercitazione, dimostreremo che la funzione `insertion_sort`
    e' corretta. La prova di correttezza deve catturare queste tre
    proprieta' della funzione `insertion_sort`:
     1) per ogni `l`, `insertion_sort l` è ordinata (Esercizio 4).
     2) per ogni `l`, tutti gli elementi di `l` appartengono a `insertion_sort l`
        (Esercizio 7)
     3) per ogni `l`, tutti gli elementi di `insertion_sort l` appartengono a `l`
    
    Ognuno dei teoremi che dimostra una delle tre proprietà necessita di
    un numero elevato di lemmi aggiuntivi. Alcuni di questi lemmi formano gli
    esercizi rimanenti. Altri vi verranno risparmiati trasformandoli in
    assiomi.
    
    NOTA BENE: non ci aspettiamo che nessuno di voi arrivi in fondo a tutti
    gli esercizi. Stupiteci! Un buon risultato consiste nel riuscire a
    completare i primi quattro.
*)


(* Esercizio 1
   ===========
   
   Lo scopo dell'esercizio è definire una funzione sorted che, presa una
   lista di naturali, restituisca true sse la lista è ordinata.

   Per definire sorted avrete bisogno di una funzione ausiliaria
   `le_first n l` che restituisce true se `l` è vuota oppure `n` è minore o
   uguale al primo elemento di `l`. Ricordatevi di definire `le_first` per
   induzione strutturale su `l`.
   
   Suggerimenti: potete utilizzare le funzioni bool_and e len definite la
   volta scorsa.
*)

let rec le_first n l on l ≝
…

let rec sorted l on l ≝
…

(* Codice di test: *)
definition one_two_three : list_nat ≝ (Cons one (Cons two (Cons three Nil))).
definition one_three_two : list_nat ≝ (Cons one (Cons three (Cons two Nil))).
theorem test_sorted_true : sorted one_two_three = true.
 done. qed.
theorem test_sorted_false1 : sorted one_three_two = false.
 done. qed.

(* Esercizio 2
   ===========
   
   Iniziano ora una serie di lemmi che culmineranno nell'esercizio 4 dove
   dimostrerete `∀l. sorted (insertion_sort l) = true`.
   
   Se una lista è ordinata, essere minore o uguale della sua testa significa
   essere minore o uguale di tutti gli elementi della lista. Di conseguenza
   vale il seguente lemma: se n è più piccolo del primo elemento di una
   lista l e anche di un nuovo elemento m inserito in l mantenendo l'ordine,
   n è più piccolo del primo elemento della nuova lista. Infatti esso è
   più piccolo sia del nuovo elemento che di tutti i vecchi.
      
   Esempio:  2 ≤ 4,  2 ≤ 3 dove 3 è la testa di 3,5,7,9
             si ha 2 ≤ 3 che è la testa di  3,4,5,7,9
             
   Dimostrate il teorema per induzione strutturale sulla lista. Notate che
   la dimostrazione NON segue il ragionamento intuitivo appena mostrato. 
*)

lemma ex2: ∀n,m. len n m = true → ∀l. le_first n l = true → le_first n (insert m l) = true.
 assume n:…
 assume m:…
 suppose (len n m = true) (Hnm).
 assume l:…
 we proceed by induction on l to prove
  (le_first n l=true→le_first n (insert m l)=true).
 case Nil.
  we need to prove
   …
  or equivalently
   …
  …
 case Cons (hd:nat) (tl:list_nat).
  by induction hypothesis we know
   … (IH).
  we need to prove
   …
  or equivalently
   (len n hd = true → le_first n (if len m hd then Cons m (Cons hd tl) else
     Cons hd (insert m tl)) = true).
  suppose … (Hnhd).
  (* L'if-then-else è sul booleano (len m hd).
     Procediamo per casi sul valore di (len m hd). *)
  we proceed by cases on (len m hd) to prove
   (len n hd = true → le_first n (if len m hd then Cons m (Cons hd tl) else
     Cons hd (insert m tl)) = true).
  case true. (* In questo caso (len m hd) è stato rimpiazzato con true *)
    (* Qui vedete nuovi comandi di Matita per dimostare l'uguaglianza E1 = En
       passando per E2, E3, ...  A ogni passaggio potete usare una semplificazione
       o dei teoremi per concludere che l'ultima espressione è uguale alla
       prossima. Per usare dei teoremi si usa il solito costrutto `by nomi`
       dopo l'uguaglianza (vedi ultimo passaggio). *)
    conclude
       (le_first n (if true then Cons m (Cons hd tl) else Cons hd (insert m tl)))
     = (le_first n (Cons m (Cons hd tl))).
     = (len n m).
     = true by Hnm
    done.
  case false. (* In questo caso (len m hd) è stato rimpiazzato con false *)
    (* Scrivete voi la catena per il caso false *)
    conclude
       (le_first n (if false then Cons m (Cons hd tl) else Cons hd (insert m tl)))
     = …
     …
qed.

(* I seguenti assiomi sono tutti dimostrabili per induzione strutturale, ma
   vi risparmiamo le loro prove assumendoli come assiomi senza dimostrarli.
   Osservate e capite bene gli enunciati tuttavia, in quanto vi torneranno utili
   nel prossimo esercizio. *)

(* n ≤ m ∨ n ≰ m *)
axiom len_ax: ∀n,m. len n m = true ∨ len n m = false.

(* se un bool_and è vero allora entrambi gli argomenti lo sono *)
axiom bool_and_to_and: ∀b1,b2. bool_and b1 b2 = true → b1 = true ∧ b2 = true.

(* se n ≰ m allora m ≤ n *)
axiom len_false: ∀n,m. len n m = false → len m n = true.


(* Esercizio 3
   ===========

   Per dimostrare l'esercizio 3 userete l'esercizio 2.

   Dimostrate un lemma chiave della correttezza della funzione insert,
   ovvero che essa inserisce un elemento in una lista ordinata rispettandone
   l'ordine. La prova è per induzione strutturale sulla lista.
*)

lemma ex3 : ∀ n, l. sorted l = true → sorted (insert n l) = true.
assume n : nat.
assume l : list_nat.
we proceed by induction on l to prove
( sorted l = true → sorted (insert n l) = true ).
 case Nil.
   …
 case Cons (n' : nat) (l' : list_nat).
  by induction hypothesis we know
   … (IH).
  we need to prove
   …
  or equivalently
   …
  suppose (bool_and (le_first n' l') (sorted l') = true) (H).
  (* qui usiamo l'assioma bool_and_to_and per spezzare l'ipotesi H in H1 + H2 *)
  by H, bool_and_to_and we have (le_first n' l' = true) (H1) and (sorted l' = true) (H2).
  by … we proved (sorted (insert n l') = true) (Hs).
  (* qui usiamo l'assioma len_ax per esplicitare n ≤ n' ∨ n ≰ n' per poi ragionare
     per casi. Andare per casi aiuta a sbloccare l'if-then-else *)
  by len_ax we proved (len n n' = true ∨ len n n' = false) (C).
  we proceed by cases on C to prove
   (sorted (if len n n' then Cons n (Cons n' l') else Cons n' (insert n l')) = true).
  case Left.
    (* usate di nuovo le catene di uguaglianze *)
    conclude
      (sorted (if len n n' then Cons n (Cons n' l') else Cons n' (insert n l')))
    = …
    = true
  done.
  case Right.
    (* i prossimi due passaggi dimostrano un'uguaglianza che tornerà utile
       nella catena *)
    by len_false, H3 we proved (len n' n = true) (H4).
    by … we proved (le_first n' (insert n l') = true) (H5).
    (* ora basta fare una catena fino alla fine della prova *)
    conclude
    …
qed.

(* Esercizio 4
   ===========
   
   Dimostrate ora che l'output dell'insertion_sort è sempre ordinato.
   
   Dovrete utilizzare l'esercizio 3 durante la dimostrazione.
*)

theorem ex4 : ∀l. sorted (insertion_sort l) = true.
…
qed.

(* La proprietà dell'esercizio 4 da sola non garantisce la correttezza
   dell'insertion_sort come algoritmo di ordinamento. In effetti il codice
   bacato che ignora l'input e restituisce sempre la lista 1,2,3,4 soddisfa
   l'enunciato dell'esercizio 4.
   
   Pertanto un algoritmo di ordinamento è corretto quando, oltre a restituire
   una lista ordinata, restituisce una lista che ha gli stessi elementi di
   quella in input.
   
   Iniziamo ora a dimostrare tale proprietà. *)


(* La eqn restituisce true solamente quando i due input sono uguali.
   È facilmente dimostrabile per induzione strutturale, ma la prova è
   lunga e ve la risparmiamo. *)
axiom eqn_to_eq : ∀ n, m. eqn n m = true → n = m.

(* Esercizio 5
   ===========
   
   Definire per ricorsione strutturale il predicato `member n l` che 
   restituisce `true` se e solo se il naturale `n` appartiene alla
   lista `l`.
   
   Il predicato servirà in seguito per asserire che tutti gli elementi
   di una lista sono nella lista ordinata e viceversa.
   
   Suggerimento: usare la funzione `eqn`,
     e ricordare la notazione `if ... then ... else ...`
*)

…

(* I seguenti quattro assiomi sono tutti dimostrabili per induzione
   strutturale. Ve li risparmiamo, ma sono esempi di esercizi interessanti. *)
axiom member_hd: ∀n,tl. member n (Cons n tl) = true.
axiom member_tl: ∀n,hd,tl. member n tl = true → member n (Cons hd tl) = true.
axiom member_Nil: ∀n. ¬(member n Nil = true).
axiom member_Cons:
 ∀n,hd,tl. member n (Cons hd tl) = true →
  n = hd ∨ member n tl = true.

(* Esercizio 6
   ===========

   Un altro esempio di lemma intuitivamente ovvio, ma brigoso da dimostrare
   per induzione strutturale. Ovvero: l'elemento inserito in una lista
   appartiene alla lista prodotta in output.
   
   Suggerimento: se a un certo punto vi ritrovate a ragionare su un'espressione
   contenente un `if len n hd then .. else ..` potete procedere come segue
   
   we proceed by cases on (len n hd) to prove ...
   case true.
     ...
   case false
     ...
     
   come nell'esercizio 2
*)
   
theorem ex6: ∀n,l. member n (insert n l) = true.
 …
qed.

(* L'esercizio 6 asseriva che aggiungendo un elemento a una lista esso
   effettivamente appare nell'output. Il seguente assioma asserisce che, quando
   si aggiunge un elemento a una lista, nessuno degli elementi presenti in
   precedenza viene perduto.
   
   La dimostrazione sarebbe simile a quella dell'esercizio 6, ma molto più lunga.
   Ve la risparmiamo con un assioma. *)
axiom mem_insert: ∀n,m,l. member n l = true → member n (insert m l) = true.


(* Esercizio 7
   ===========
   
   Siamo finalmente pronti a dimostrare la seconda proprietà dell'ordinamento:
   tutti gli elementi da ordinare sono presenti nella lista ordinata in output.
   
   Suggerimento: quando vi ritrovate con un'ipotesi
   
      suppose (member n (Cons hd tl) = true) (I).
      
   potete combinarla con l'assioma member_Cons così
   
      by I, member_Cons we proved (n=hd ∨ member n tl = true) (I2).
      
   per poi procedere per casi
   
      we proceed by cases on I2 to prove ....
      case Left.
         ...
      case Right.
         ...
         
   Nei due rami (Left e Right) attenzione alla nuova ipotesi a disposizione
   (guardate la finestra di Matita in altro a dx)
*)

lemma ex7 : ∀ n, l. member n l = true → member n (insertion_sort l) = true.
…
qed.

(* Le fatiche del bravo implementatore non sono finite: il codice potrebbe
   ancora essere bacato e inserire in output dei numeri non presenti in input.
   
   Per essere sicuri che non accada bisogna dimostrare il viceversa.
   Se volete cercare di dimostrarlo, ricordatevi che avrete bisogno di
   dimostrare un certo numero di nuovi lemmi.
*)

axiom ex7_dual : ∀ n, l. member n (insertion_sort l) = true → member n l = true.

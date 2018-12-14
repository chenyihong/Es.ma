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

   Consegnare con il solito comando
   ~sacerdot/logica1819/ConsegnaLogica NOMEFILE.ma

*)



(* ATTENZIONE
   ==========
   
   Non modificare quanto segue 
*)
include "nat/minus.ma".
definition if_then_else ≝ λT:Type.λe,t,f.match e return λ_.T with [ true ⇒ t | false ⇒ f].
notation > "'if' term 19 e 'then' term 19 t 'else' term 90 f" non associative with precedence 19 for @{ 'if_then_else $e $t $f }.
notation < "'if' \nbsp term 19 e \nbsp 'then' \nbsp term 19 t \nbsp 'else' \nbsp term 90 f \nbsp" non associative with precedence 19 for @{ 'if_then_else $e $t $f }.
interpretation "Formula if_then_else" 'if_then_else e t f = (if_then_else ? e t f).
definition max ≝ λn,m. if eqb (n - m) 0 then m else n. 
definition min ≝ λn,m. if eqb (n - m) 0 then n else m. 

(* Ripasso
   =======
   
   Il linguaggio delle formule, dove gli atomi sono
   rapperesentati da un numero naturale
*)
inductive Formula : Type ≝
| FBot: Formula
| FTop: Formula
| FAtom: nat → Formula
| FAnd: Formula → Formula → Formula
| FOr: Formula → Formula → Formula
| FImpl: Formula → Formula → Formula
| FNot: Formula → Formula
.

(* Esercizio 1
   ===========
   
   Nel seguito assumere che i mondi restituiscano sempre solamente 0 o 1
   introdurrebbe alcune complicazioni. Ci semplifichiamo tecnicamente la vita
   assumendo che tutti i numeri naturali >= 1 restituiti da un mondo significhino
   denotino il vero e forziamo invece la semantica di una formula a tornare
   sempre 0 o 1.
   
   Modificare la funzione `sem` scritta nella precedente
   esercitazione in modo che valga solo 0 oppure 1 nel caso degli
   atomi, anche nel caso in cui il mondo `v` restituisca un numero
   maggiore di 1.
   
   Suggerimento: non è necessario usare il costrutto if_then_else
   e tantomento il predicato di maggiore o uguale. È invece possibile
   usare la funzione `min`.
*) 
let rec sem (v: nat → nat) (F: Formula) on F : nat ≝
 match F with
  [ FBot ⇒ 0
  | FTop ⇒ 1
  | FAtom n ⇒ min …
  | FAnd F1 F2 ⇒ min (sem v F1) (sem v F2)
  | FOr F1 F2 ⇒ max (sem v F1) (sem v F2)
  | FImpl F1 F2 ⇒ max (1 - sem v F1) (sem v F2)
  | FNot F1 ⇒ 1 - (sem v F1)
  ]
.

(* ATTENZIONE
   ==========
   
   Non modificare quanto segue.
*)
notation < "[[ \nbsp term 19 a \nbsp ]] \nbsp \sub term 90 v" non associative with precedence 90 for @{ 'semantics $v $a }.
notation > "[[ term 19 a ]] \sub term 90 v" non associative with precedence 90 for @{ 'semantics $v $a }.
notation > "[[ term 19 a ]] term 90 v" non associative with precedence 90 for @{ sem $v $a }.
interpretation "Semantic of Formula" 'semantics v a = (sem v a).

definition v20 ≝ λx.
       if eqb x 0 then 2
  else if eqb x 1 then 1
  else                 0.
  
(* Test 1
   ======
   
   La semantica della formula `(A ∨ C)` nel mondo `v20` in cui 
   `A` vale `2` e `C` vale `0` deve valere `1`.
*)    

lemma test1: [[FOr (FAtom 0) (FAtom 2)]]v20 = 1.
 done.
qed. 



(* ATTENZIONE
   ==========
   
   Non modificare quanto segue.
*)
lemma sem_bool : ∀F,v. [[ F ]]v = 0 ∨ [[ F ]]v = 1.  intros; elim F; simplify; [left;reflexivity; |right;reflexivity; |cases (v n);[left;|cases n1;right;]reflexivity; |4,5,6: cases H; cases H1; rewrite > H2; rewrite > H3; simplify; first [ left;reflexivity | right; reflexivity ].  |cases H; rewrite > H1; simplify;[right|left]reflexivity;] qed.
lemma min_bool : ∀n. min n 1 = 0 ∨ min n 1 = 1.  intros; cases n; [left;reflexivity] cases n1; right; reflexivity; qed.  
lemma min_max : ∀F,G,v.  min (1 - [[F]]v) (1 - [[G]]v) = 1 - max [[F]]v [[G]]v.  intros; cases (sem_bool F v);cases (sem_bool G v); rewrite > H; rewrite >H1; simplify; reflexivity; qed.
lemma max_min : ∀F,G,v.  max (1 - [[F]]v) (1 - [[G]]v) = 1 - min [[F]]v [[G]]v.  intros; cases (sem_bool F v);cases (sem_bool G v); rewrite > H; rewrite >H1; simplify; reflexivity; qed.
lemma min_1_1 : ∀x.x ≤ 1 → 1 - (1 - x) = x. intros; inversion H; intros; destruct; [reflexivity;] rewrite < (le_n_O_to_eq ? H1); reflexivity;qed.
lemma sem_le_1 : ∀F,v.[[F]]v ≤ 1. intros; cases (sem_bool F v); rewrite > H; [apply le_O_n|apply le_n]qed.

(* Esercizio 2
   ===========
   
   Definire per ricorsione strutturale la funzione `negate`
   che presa una formula `F` ne nega gli atomi.
   
   Ad esempio la formula `(A ∨ (⊤ → B))` deve diventare
   `¬A ∨ (⊤ → ¬B)`.
*)
let rec negate (F: Formula) on F : Formula ≝
 match F with
  [ …
  ].

lemma test2: negate (FOr (FAtom 0) (FImpl FTop (FAtom 1))) = FOr (FNot (FAtom 0)) (FImpl FTop (FNot (FAtom 1))).
 done.
qed.
(* ATTENZIONE
   ==========
   
   Non modificare quanto segue
*)
definition equiv ≝ λF1,F2. ∀v.[[ F1 ]]v = [[ F2 ]]v.
notation "hvbox(a \nbsp break mstyle color #0000ff (≡) \nbsp b)"  non associative with precedence 45 for @{ 'equivF $a $b }.
notation > "a ≡ b" non associative with precedence 50 for @{ equiv $a $b }.
interpretation "equivalence for Formulas" 'equivF a b = (equiv a b).
lemma equiv_rewrite : ∀F1,F2,F3. F1 ≡ F2 → F1 ≡ F3 → F2 ≡ F3. intros; intro; autobatch. qed.

(* Esercizio 3
   ===========
   
   Definire per ricorsione strutturale la funzione di
   dualizzazione di una formula `F`. Tale funzione:
   
   * Scambia FTop con FBot e viceversa
   
   * Scambia il connettivo FAnd con FOr e viceversa
   
   * Sostituisce il connettivo FImpl con FAnd e nega la
     prima sottoformula. Il razionale è che `FImpl A B`
     è semanticamente equivalente a `FOr (FNot A) B` il
     cui duale è `FAnd (FNot A) B`.
   
   Ad esempio la formula `A → (B ∧ ⊥)` viene dualizzata in
   `¬A ∧ (B ∨ ⊤)`. 
*)  
let rec dualize (F : Formula) on F : Formula ≝
  match F with
  [ …
  ].

lemma test3: dualize (FImpl (FAtom 0) (FAnd (FAtom 1) FBot)) = FAnd (FNot (FAtom O)) (FOr (FAtom 1) FTop).
 done.
qed.

(* Spiegazione
   ===========
   
   La funzione `invert` permette di invertire un mondo `v`.
   Ovvero, per ogni indice di atomo `i`, se `v i` restituisce
   `1` allora `(invert v) i` restituisce `0` e viceversa.
   
*)
definition invert ≝
 λv:ℕ → ℕ. λx. if eqb (min (v x) 1) 0 then 1 else 0.
 
interpretation "Inversione del mondo" 'invert v = (invert v).
 


(* Esercizio 4
   ===========
   
   Dimostrare il lemma `negate_invert` che asserisce che
   la semantica in un mondo `v` associato alla formula
   negata di `F` e uguale alla semantica associata
   a `F` in un mondo invertito.
*) 
lemma negate_invert:
  ∀F:Formula.∀v:ℕ→ℕ.[[ negate F ]]v=[[ F ]](invert v).
assume F:Formula.
assume v:(ℕ→ℕ).
we proceed by induction on F to prove ([[ negate F ]]v=[[ F ]](invert v)).
  case FBot.
    …
  done.
  case FTop.
    …
  done.
  case FAtom.
    assume n : ℕ.
    the thesis becomes (…).
    the thesis becomes (…).
    the thesis becomes (1 - (min (v n) 1)= min (if eqb (min (v n) 1) 0 then 1 else 0) 1).
    by min_bool we proved (min (v n) 1 = 0 ∨ min (v n) 1 = 1) (H1);
    we proceed by cases on (H1) to prove (1 - (min (v n) 1)= min (if eqb (min (v n) 1) 0 then 1 else 0) 1).
      case Left.
        conclude 
            (1 - (min (v n) 1)) 
          = (1 - 0) by H.
          = 1.
          = (min 1 1).
          = (min (if true then 1 else O) 1).
          = (min (if eqb 0 0 then 1 else O) 1).
          = (min (if eqb (min (v n) 1) O then 1 else O) 1) by H.
      done.
      case Right.
        …
      done.
  case FAnd.
    assume f : Formula.
    by induction hypothesis we know
      (…) (H).
    assume f1 : Formula.
    by induction hypothesis we know
     (…) (H1).
    the thesis becomes
     ([[ negate (FAnd f f1) ]]v=[[ FAnd f f1 ]](invert v)).
    the thesis becomes
     (min [[ negate f ]]v [[ negate f1]]v = [[ FAnd f f1 ]](invert v)).
    conclude 
        (min [[ negate f ]]v [[ negate f1]]v)
      = (min [[ f ]](invert v) [[ negate f1]]v) by ….
      = (min [[ f ]](invert v) [[ f1]](invert v)) by ….
  done.
  case FOr.
    …
  done.
  case FImpl.
    …
  done.
  case FNot.
    …
  done.  
qed.   

(* Esercizio 5
   ===========
   
   Dimostrare che la funzione negate rispetta l'equivalenza.
*)
lemma negate_fun:
 ∀F:Formula.∀G:Formula.F ≡ G → negate F ≡ negate G.
 assume ….
 assume ….
 suppose ….
 the thesis becomes ….
 the thesis becomes ….
 assume v:(ℕ→ℕ).
 conclude 
     [[ negate F ]]v
   = [[ F ]](invert v) by ….
   = [[ G ]](….
 done.  
qed.

(* Esercizio 6
   ===========
   
   Dimostrare che per ogni formula `F`, `(negate F)` equivale a 
   dualizzarla e negarla.
*)
lemma not_dualize_eq_negate:
 ∀F:Formula.negate F ≡ FNot (dualize F).
 …
 assume v:(ℕ→ℕ).
 we proceed by induction on F to prove ([[negate F]]v=[[FNot (dualize F)]]v).
 case FBot.
   …
 done.
 case FTop.
   …
 done.
 case FAtom.
   …
 done.
 case FAnd.
   assume f : Formula.
   by induction hypothesis we know
     ([[ negate f ]]v=[[ FNot (dualize f) ]]v) (H).
   assume f1 : Formula.
   by induction hypothesis we know
    ([[ negate f1 ]]v=[[ FNot (dualize f1) ]]v) (H1).
   the thesis becomes
    ([[ negate (FAnd f f1) ]]v=[[ FNot (dualize (FAnd f f1)) ]]v).
   the thesis becomes
    (min [[ negate f ]]v [[ negate f1 ]]v=[[ FNot (dualize (FAnd f f1)) ]]v).
   conclude 
       (min … …)
     = (min … …) by H.    
     = (min … …) by H1.
     = (min (1 - [[ dualize f ]]v) (1 - [[ dualize f1 ]]v)).
     = (1 - (max [[ dualize f ]]v [[ dualize f1 ]]v)) by min_max.
 done.
 case FOr.
   …
 done.
 case FImpl.
   …
 done.
 case FNot.
   …
 done.
qed.

(* Esercizio 7
   ===========
   
   Dimostrare che la negazione è iniettiva
*)
theorem not_inj:
 ∀F,G:Formula.FNot F ≡ FNot G→F ≡ G.
 …
 assume v:(ℕ→ℕ).
 by sem_le_1 we proved ([[F]]v ≤ 1) (H1).
 by … we proved ([[G]]v ≤ 1) (H2).
 by min_1_1, H1 we proved (1 - (1 - [[F]]v) = [[F]]v) (H3).
 by … we proved (… = [[G]]v) (H4).
 conclude 
     ([[F]]v)
   = (1 - (1 - [[F]]v)) by ….
   = (1 - [[…]]v).
   = (1 - [[ FNot G]]v) by H.
   = (1 - …).
   = [[G]]v by ….
 done.
qed.



(* Esercizio 8
   ===========
   
   Dimostrare il teorema di dualità
*)
theorem duality: ∀F1,F2:Formula.F1 ≡ F2 → dualize F1 ≡ dualize F2.
 assume F1:Formula.
 assume F2:Formula.
 suppose (F1 ≡ F2) (H).
 the thesis becomes (dualize F1 ≡ dualize F2).
 by …, H we proved (negate F1 ≡ negate F2) (H1).
 by …, …, H1 we proved (FNot (dualize F1) ≡ negate F2) (H2).
 by …, …, H1, H2 we proved (FNot (dualize F1) ≡ FNot (dualize F2)) (H3).
 by …, H3 we proved (dualize F1 ≡ dualize F2) (H4).
 by H4 done.
qed.
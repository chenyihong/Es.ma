(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)


(*

 Componenti del gruppo (completare):

 * Nome1: ...
 * Cognome1: ...
 * Numero di matricola1: ...

 * Nome2: ...
 * Cognome2: ...
 * Numero di matricola2: ...

*)

(* Saltate le righe seguenti dove vengono dati gli assiomi e definite
   le notazioni e cercate Exercise 1. *)

include "logic/connectives.ma".
include "logic/equality.ma".

notation "hvbox(A break ⇔ B)" left associative with precedence 30 for
@{'iff $A $B}.
interpretation "iff" 'iff A B = (iff A B).

(* set, ∈ *)
axiom set: Type.
axiom mem: set → set → Prop.
axiom incl: set → set → Prop.

notation "hvbox(a break ∈ U)" non associative with precedence 50 for
@{'mem $a $U}.
interpretation "mem" 'mem = mem.

notation "hvbox(a break ⊆ U)" non associative with precedence 50 for
@{'incl $a $U}.
interpretation "incl" 'incl = incl.

(* Extensionality *)
axiom ax_extensionality: ∀A, B. (∀Z. Z ∈ A ⇔ Z ∈ B) → A = B.

(* Inclusion *)
axiom ax_inclusion1: ∀A, B. A ⊆ B → (∀Z. Z ∈ A → Z ∈ B).
axiom ax_inclusion2: ∀A, B. (∀Z. Z ∈ A → Z ∈ B) → A ⊆ B.

(* Emptyset  ∅ *)
axiom emptyset: set.

notation "∅" non associative with precedence 90 for @{'emptyset}.
interpretation "emptyset" 'emptyset = emptyset.

axiom ax_empty: ∀X. ¬(X ∈ ∅).

(* Intersection ∩ *)
axiom intersect: set → set → set.

notation "hvbox(A break ∩ B)" left associative with precedence 80 for
@{'intersect $A $B}.
interpretation "intersect" 'intersect = intersect.

axiom ax_intersect1: ∀A,B. ∀Z. (Z ∈ A ∩ B → Z ∈ A ∧ Z ∈ B).
axiom ax_intersect2: ∀A,B. ∀Z. (Z ∈ A ∧ Z ∈ B → Z ∈ A ∩ B).

(* Union ∪ *)
axiom union: set → set → set.

notation "hvbox(A break ∪ B)" left associative with precedence 70 for
@{'union $A $B}.
interpretation "union" 'union = union.

axiom ax_union1: ∀A,B. ∀Z. (Z ∈ A ∪ B → Z ∈ A ∨ Z ∈ B).
axiom ax_union2: ∀A,B. ∀Z. (Z ∈ A ∨ Z ∈ B → Z ∈ A ∪ B).

notation "ABSURDUM A" non associative with precedence 89 for @{'absurdum $A}.
interpretation "ex_false" 'absurdum A = (False_ind ? A).

(* Da qui in avanti riempite i puntini e fate validar quello che scrivete
   a Matita usando le icone con le frecce. *)

(* Exercise 1 *)
theorem union_inclusion: ∀A, B. A ⊆ A ∪ B.
  assume A: set.
  assume B: set.
  we need to prove (∀Z. Z ∈ A → Z ∈ A ∪ B) (I).
    assume Z: set.
    suppose … (ZA).
    we need to prove (Z ∈ A ∨ Z ∈ B) (I1).
    by … we proved (Z ∈ A ∨ Z ∈ B) (Zor).
    by Zor,ax_union2 done.
  by I1,ax_union2 done.
  by … done.
qed.

(* Exercise 2 *)
theorem union_idempotent: ∀A. A ∪ A = A.
 assume A: set.
 we need to prove (∀Z. Z ∈ A ∪ A ⇔ Z ∈ A) (II).
  assume Z: ….
  we need to prove (Z ∈ A ∪ A → Z ∈ A) (I1).
   suppose … (Zu).
   by … we proved (Z ∈ A ∨ Z ∈ A) (Zor).
   we proceed by cases on Zor to prove (Z ∈ A).
    case left.
     by H
    done.
    case right.
     by …
  done.
  we need to prove … (I2).
   suppose (Z ∈ A) (ZA).
   by ZA, or_introl we proved … (Zor).
   by Zor, ax_union2 
  done.
  by …
 done.
 by …
done.
qed.

(* Exercise 3 *)
theorem intersection_idempotent: ∀A. A ∩ A = A.
 assume A: set.
 we need to prove (∀Z. Z ∈ A ∩ A ⇔ Z ∈ A) (II).
  assume Z: set.
  we need to prove … (I1).
   suppose … (Zi).
   by ax_intersect1, Zi we have (Z ∈ A) (ZA1) and (Z ∈ A) (ZA2).
   by …
  done.
  we need to prove … (I2).
   suppose (Z ∈ A) (ZA).
   by ZA, conj we proved (Z ∈ A ∧ Z ∈ A) (Zand).
   by …
  done.
  by I1,I2,conj
 done.
 by …
done.
qed.

(* Exercize 4 *)
theorem empty_absurd: ∀X, A. X ∈ ∅ → X ∈ A.
 assume X: …. 
 assume A: ….
 suppose … (XE).
 by … we proved False (bottom).
 by (ABSURDUM bottom) 
done.
qed.
  
(* Exercise 5 *)
theorem intersect_empty: ∀A. A ∩ ∅ = ∅.
 assume A: set.
 we need to prove … (II).
   assume Z: set.
   we need to prove … (I1).
     suppose … (Ze).
     we need to prove (Z ∈ ∅).
     by Ze,ax_intersect1 we have (Z ∈ A) (ZA) and … (ZE).
     by ZE
   done.
   we need to prove … (I2).
     suppose … (ZE).
     by ZE, ax_empty we proved False (bottom).
     by … done.
   by I1,I2,conj
 done.
 by …,…
done.
qed.

(* Exercise 6 *)
theorem union_empty: ∀A. A ∪ ∅ = A.
 assume A: set.
 we need to prove … (II).
   assume Z: set.
   we need to prove … (I1).
     suppose … (ZA).
     by …,or_introl we proved … (Zor).
     by ax_union2,Zor
   done.
   we need to prove … (I2).
     suppose … (Zu).
     by Zu, … we proved (Z ∈ A ∨ Z ∈ ∅) (Zor).
     we proceed by cases on … to prove (Z ∈ A).
      case left.
       by … 
      done.
      case right.
       by … we proved False (bottom).
       by (ABSURDUM …) 
      done.
    by …
  done.
  by …
 done.
qed.

(* Exercise 7 *)
theorem intersect_commutative: ∀A,B. A ∩ B = B ∩ A.
 assume A: set.
 assume B: set.
 we need to prove (∀Z. Z ∈ A ∩ B ⇔ Z ∈ B ∩ A) (II).
   assume Z: set.
   we need to prove … (I1).
     suppose … (ZAB).
     we need to prove (Z ∈ B ∩ A).
      by …,ZAB we have (Z ∈ A) (ZA) and (Z ∈ B) (ZB).
      by …,conj,ZB,ZA
   done.
   we need to prove … (I2).
     suppose … (ZBA).
     we need to prove ….
     by …,ZBA we have (Z ∈ B) (ZB) and … (ZA).
     by …,conj,ZA,ZB
   done.
   by conj,I1,I2
 done.
 by …,II
done.
qed.

(* Exercise 8 *)
theorem union_commutative: ∀A,B. A ∪ B = B ∪ A.
 assume A: set.
 assume B: set.
 we need to prove … (II).
   assume Z: set.
   we need to prove … (I1).
     suppose … (ZAB).
     we need to prove (Z ∈ B ∪ A).
     we need to prove (Z ∈ B ∨ Z ∈ A) (I).
       by ax_union1,ZAB we proved … (Zor).
       we proceed by cases on Zor to prove ….
         case or_introl.
           by H,…
         done.
         case or_intror.
            by H,…
         done.
     by …,I
   done.
   we need to prove … (I2).
     suppose … (ZBA).
     we need to prove ….
     we need to prove (Z ∈ A ∨ Z ∈ B) (I).
       by ax_union1,ZBA we proved … (Zor).
       we proceed by cases on … to prove (Z ∈ A ∨ Z ∈ B).
         case or_introl.
           by H,…
         done.
         case or_intror.
            by H,…
         done.
     by …,I
   done.
   by …
 done.        
 by …,II
done.
qed.

(* Exercise 9 *)
theorem distributivity1: ∀A,B,C. A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
 assume A: set.
 assume B: set.
 assume C: set.
 we need to prove … (II).
  assume Z:set.
  we need to prove … (I1).
   suppose … (Zint).
   by Zint, … we have … (Zu1) and … (Zu2).
   by Zu1, … we proved … (Zor1).
   by Zu2, … we proved … (Zor2).
   we proceed by cases on Zor1 to prove ….
   case A.
    by or_introl,H,… 
    done.
   case B.
    we proceed by cases on Zor2 to prove ….
    case A.
     by or_introl,H1,ax_union2 
    done.
    case C.
     by H,H1,conj,ax_intersect2 we proved … (K1).
     by K1,or_intror,ax_union2 
  done.
  we need to prove … (I2).
   assume Z: set.
   suppose … (Zu).
   by Zu,ax_union1 we proved … (Zor).
   we proceed by cases on Zor to prove ….
   case A.
    by H,… we proved (Z∈(A∪B)) (K1).
    by H,… we proved (Z∈(A∪C)) (K2).
    by … 
   done.
   case BC.
    by …,H  we have (Z ∈ B) (H1) and (Z ∈ C) (H2).
    by … we proved (Z∈(A∪B)) (K1).
    by … we proved (Z∈(A∪C)) (K2).
    by …
  done.
  by … 
 done.
 by … 
done. 
qed.

(* Exercise 10 *)
theorem distributivity2: ∀A,B,C. A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
 assume A: set.
 assume B: set.
 assume C: set.
 we need to prove … (II).
  assume ….
  we need to prove … (I1).
   suppose … (K1).
   by … we have … (K1A) and … (K1BC).
   by … we proved … (Zor).
   we proceed by cases on (Zor) to prove ….
   case B.
    by … we proved … (H1).
    by … 
   done.
   case C.
    by … we proved … (H1).
    by … 
  done.
  …
  by I1,…,conj
 done.
 by II,ax_extensionality
done.
qed.

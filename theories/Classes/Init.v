(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Initialization code for typeclasses, setting up the default tactic
   for instance search.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

(** Hints for the proof search: these combinators should be considered rigid. *)

Require Import Corelib.Program.Basics.

Global Typeclasses Opaque id const flip compose arrow impl iff not all.

(** Apply using the same opacity information as typeclass proof search. *)

Ltac class_apply c := autoapply c with typeclass_instances.

(** The unconvertible typeclass, to test that two objects of the same type are
   actually different. *)
#[universes(polymorphic)]
Class Unconvertible (A : Type) (a b : A) := unconvertible : unit.

Ltac unconvertible :=
  match goal with
    | |- @Unconvertible _ ?x ?y => unify x y with typeclass_instances ; fail 1 "Convertible"
    | |- _ => exact tt
  end.

#[global]
Hint Extern 0 (@Unconvertible _ _ _) => unconvertible : typeclass_instances.

Require Import Ltac2.Ltac2.

Ltac2 Type 'a foo := { a : 'a; b : 'a }.

Ltac2 foo1 () := { { a := (); b := () } with a := () }.

Fail Ltac2 foo2 () := { { a := (); b := () } with a := 2 }.

Ltac2 Type ('a,'b) bar := { aa : 'a; bb : 'b }.

Ltac2 bar1 () := { { aa := (); bb := () } with aa := () }.

Ltac2 bar2 () := { { aa := (); bb := () } with aa := 2 }.

Fail Ltac2 foobar () := { { a := (); b := () } with aa := () }.

Ltac2 varvar v := { v with aa := () }.
Print varvar.

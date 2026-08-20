From Peregrine.Plugin Require Import Loader.
From Peregrine.Tests Require Demo.
From Peregrine.Tests Require Hello.
From Peregrine.Tests Require Map.
From Peregrine.Tests Require Mutual.
From Peregrine.Tests Require Nat.
From Peregrine.Tests Require OddEven.
From Peregrine.Tests Require CatCryptAdd.
From Peregrine.Tests Require CatCryptConst.
From Peregrine.Tests Require CatCryptShare.
From Peregrine.Tests Require CatCryptShift.

(* Demo.v *)
Peregrine Extract "extraction/Demo.ast" Demo.test.
Peregrine Extract Typed "extraction/Demo_typed.ast" Demo.test.

(* Hello.v *)
Peregrine Extract "extraction/Hello.ast" Hello.hello.
Peregrine Extract Typed "extraction/Hello_typed.ast" Hello.hello.

(* Map.v *)
Peregrine Extract "extraction/Map.ast" Map.ys.
Peregrine Extract Typed "extraction/Map_typed.ast" Map.ys.

(* Mutual.v *)
Peregrine Extract "extraction/Mutual.ast" Mutual.test.
Peregrine Extract Typed "extraction/Mutual_typed.ast" Mutual.test.

(* Nat.v *)
Peregrine Extract "extraction/Nat.ast" Nat.thing.
Peregrine Extract Typed "extraction/Nat_typed.ast" Nat.thing.

(* OddEven.v *)
Peregrine Extract "extraction/OddEven.ast" OddEven.test.
Peregrine Extract Typed "extraction/OddEven_typed.ast" OddEven.test.

(* CatCryptAdd.v *)
Peregrine Extract "extraction/CatCryptAdd.ast" CatCryptAdd.add3.
Peregrine Extract "extraction/CatCryptAddClosed.ast" CatCryptAdd.add3_closed.

(* CatCryptConst.v *)
Peregrine Extract "extraction/CatCryptConst.ast" CatCryptConst.addc.
Peregrine Extract "extraction/CatCryptConstClosed.ast" CatCryptConst.addc_closed.

(* CatCryptShare.v *)
Peregrine Extract "extraction/CatCryptShare.ast" CatCryptShare.sq2.
Peregrine Extract "extraction/CatCryptShareClosed.ast" CatCryptShare.sq2_closed.

(* CatCryptShift.v *)
Peregrine Extract "extraction/CatCryptShift.ast" CatCryptShift.mix.
Peregrine Extract "extraction/CatCryptShiftClosed.ast" CatCryptShift.mix_closed.

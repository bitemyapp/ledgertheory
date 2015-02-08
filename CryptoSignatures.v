(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** CryptoSignatures: The trivial code here simulates cryptographic signatures
    using a module that exports a type of signatures and a relation check_signat.
    There are some additional functions and properties exported that are not used
    in the rest of the development.
 **)

Require Export CryptoHashes.

Module Type SignatType.

  Parameter signat : Type.
  Parameter privkey : Type.
  Parameter privkey_addr : privkey -> addr.
  Parameter sign : privkey -> hashval -> nat -> signat.
  Parameter check_signat : hashval -> signat -> addr -> Prop.

  Axiom privkey_addr_inj : forall key key', privkey_addr key = privkey_addr key' -> key = key'.
  Axiom signat_prop : forall r key alpha h, privkey_addr key = alpha -> check_signat h (sign key h r) alpha.

End SignatType.

Module Signat : SignatType.

  Definition signat := unit.
  Definition privkey := addr.
  Definition privkey_addr : privkey -> addr := fun alpha => alpha.
  Definition sign : privkey -> hashval -> nat -> signat := fun _ _ _ => tt.
  Definition check_signat : hashval -> signat -> addr -> Prop := fun _ _ _ => True.

  Theorem privkey_addr_inj (key key':privkey) : privkey_addr key = privkey_addr key' -> key = key'.
    intros H. exact H.
  Qed.

  Theorem signat_prop r key alpha h : privkey_addr key = alpha -> check_signat h (sign key h r) alpha.
    intros _. unfold check_signat. tauto.
  Qed.

End Signat.

Export Signat.


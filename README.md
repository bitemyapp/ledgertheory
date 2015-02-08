# ledgertheory

## Ledger Theory Coq Development

This repository contains a Coq development of a theory of lightweight cryptographic ledgers.
The files should be compiled in the following order (see also the file coqcompile):

Prelude.v
Addrs.v
CryptoHashes.v 
CryptoSignatures.v 
Assets.v
Transactions.v
LedgerStates.v
MTrees.v
CTrees.v
CTreeGrafting.v
Blocks.v

## White Paper

There is also a white paper lightcrypto.pdf providing a high level description and overview
of what is here. More detailed descriptions of the various parts will hopefully be written soon.

## License

This is all being released as open source under the MIT/X11 software license.
See http://www.opensource.org/licenses/mit-license.php
This is also in the file LICENSE along with a bitcoin signature of the license.

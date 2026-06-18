# CompElliptic

This directory contains a vendored subset of Daira-Emma Hopwood's CompElliptic
formalization:

https://github.com/daira/CompElliptic

The code here is a theorem backend for elliptic-curve and finite-field facts used by
the Orchard development. It is not intended to define the user-facing Orchard protocol
spec vocabulary.

Orchard-specific specs should define their own preferred types and predicates, and bridge
to these CompElliptic definitions with small compatibility lemmas when theorem support is
needed.

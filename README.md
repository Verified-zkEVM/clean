# clean

`clean` is an embedded Lean DSL for writing zk circuits, targeting AIR arithmetization.

It is developed by [zkSecurity](https://zksecurity.xyz/), currently as part of a Verified-zkEVM grant.

We intend to build out `clean` into a universal zk framework that targets all arithmetizations and produces formally verified, bug-free circuits for the entire ecosystem.

## Using the repo

Follow [official instructions](https://lean-lang.org/lean4/doc/setup.html) to install `elan` (the package manager) and Lean4.

Clone this repo, and test that everything works by building:

```bash
lake build
```

After that, we recommend open the repo in VSCode to get immediate inline feedback from the compiler while writing theorems.

Make sure to install the `lean4` extension for VSCode!

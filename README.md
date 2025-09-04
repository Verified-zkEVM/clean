<p align="center"> <img src="clean-logo-turnstilehex-greenwhite.svg" width="96" alt="Clean logo"> </p>

<h1 align="center" id="clean">Clean</h1>

`clean` is an embedded Lean DSL for writing zk circuits, targeting popular arithmetizations like AIR, PLONK and R1CS.

**Check out our blog post for an introduction: https://blog.zksecurity.xyz/posts/clean**

`clean` is developed by [zkSecurity](https://zksecurity.xyz/), currently as part of a Verified-zkEVM grant.

We intend to build out `clean` into a universal zk framework that produces **formally verified, bug-free circuits** for the entire ecosystem.

## Community

Public Telegram group to discuss `clean`: [t.me/clean_zk](https://t.me/clean_zk)

Please join if you want to use `clean`, or contribute, or if you have any questions!

We always welcome contributors! Check out our [good first issues](https://github.com/Verified-zkEVM/clean/issues?q=is%3Aissue%20state%3Aopen%20label%3A%22good%20first%20issue%22).

## Using the repo

Follow [official instructions](https://lean-lang.org/lean4/doc/setup.html) to install `elan` (the package manager) and Lean4.

Clone this repo, and test that everything works by building:

```bash
lake build
```

After that, we recommend open the repo in VSCode to get immediate inline feedback from the compiler while writing theorems.

Make sure to install the `lean4` extension for VSCode!

## Code Style

We follow standard Lean/Mathlib conventions with some local variations. See [doc/conventions.md](doc/conventions.md) for details.

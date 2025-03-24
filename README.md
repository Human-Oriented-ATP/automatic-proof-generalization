# Automatic Proof Generalization

This is supplementary material for the ITP 2025 submission _Automatically Generalizing Proofs and Statements_ containing a Lean implementation of the automatic proof generalization algorithm.

## Installation

Running the code in this repository requires a [working installation of the Lean theorem prover](https://lean-lang.org/lean4/doc/quickstart.html).

Once Lean is set up, run the command

```bash
lake exe cache get
```

in the root directory of the project to download its dependencies.

The relevant examples are in the `Demo.lean` file in the top-level directory of this folder.

### Troubleshooting
VSCode sometimes shows a red bar when first opening a Lean file. If this happens, reload the file using Control+Shift+X (or Command-Shift+X on Mac).

If the Lean files take more than a couple of minutes to run, try cleaning the cache with `lake clean` and then redownloading with `lake exe cache get`.


# Gravity

*Bending Trustspace.*

Gravity proves [DMP, the Dark Matter Protocol](https://github.com/StevenHrovat/dmp). DMP states the axioms; [IM, the Interstellar
Medium](https://github.com/StevenHrovat/im) is the interface that makes them sound; [CM, Canis Major](https://github.com/StevenHrovat/cm)
is what makes IM do that. Gravity checks the whole chain in both directions, the gravitational wave test of DMP chapter 06: two
independent detectors must agree before a layer counts as proven.

- **The DMP it proves:** [`vendor/dmp/`](vendor/README.md), DMP byte for byte at one pinned commit (DMP chapter 00, "The root chain":
  Gravity holds the version of DMP it is based on). `tools/check-pin.sh` refuses a copy that no longer matches its PIN. The version is the
  one in `vendor/dmp/VERSION`; every sentence a theorem is stated from is read there, never from the network.
- **Down (intent chain):** Gravity's own models, from DMP's sentences down to CM. Not in this repository yet.
- **Up (evidence chain):** [`evidence/`](evidence/README.md), proofs in Lean 4 (core only, no Mathlib) from the code up to DMP's
  sentences. Every theorem is proved; `evidence/tools/check.sh` checks the pin, builds the project and asks Lean's kernel which axioms
  each theorem rests on, and CI re-checks the export with a second kernel written separately (nanoda).

The two chains never import or name each other's files. On a mismatch the stricter answer stands.

## Run it

```sh
tools/check-pin.sh                                   # the vendored DMP matches its PIN (needs only bash, find, sha256sum)
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain "$(cat evidence/lean-toolchain)"
evidence/tools/check.sh                              # runs the pin check first, then the Lean chain
```

Where `release.lean-lang.org` is not reachable, the same toolchain is the GitHub release asset
`https://github.com/leanprover/lean4/releases/download/<tag>/lean-<version>-linux.tar.zst`; unpack it and put its `bin/` on the PATH.

CI: `lean-evidence` (build, axiom report, independent kernel) and `scrub-scan` (no company data, no secrets) on GitHub-hosted runners.

Licensed under the Apache License 2.0 ([LICENSE](LICENSE)).

# Spark cold verification

The exact frozen source ZIP was independently extracted into an empty local NVMe project on Linux ARM64. Lean 4.33.1 built all 93 local project modules with warnings treated as errors. The verifier cross-checked the local imports resolved by Lean and ran 93 separate `leanchecker` processes. The nine external Git checkouts matched the dependency lock. They were supplied through a separate copy of the existing dependency cache.

The lexical source scan passed. The 92 source reports and 11 additional targeted reports used only `propext`, `Classical.choice` and `Quot.sound`. `module-receipts.tsv` and `axioms.tsv` contain the exact module digests and declarations. `STATEMENT-MAP.md` maps the all-size threshold-two window and its sharpness to the original rows.

- Source ZIP SHA-256 `ec9deee2dc302459b371b7931abc50c3ee6ab6ff526a112074ef2de96271a825`
- Entry source SHA-256 `9afe1bdd8bcc1b6a50ddc553ff3fbdf143dabca2e799684117d59c0a5eec5877`
- Cold log SHA-256 `1e6680394c19f65e0ff3f5676acdec22a4e74ee0beee50f26172a50f05320f91`

Use `python3 -B run-cold.py /absolute/path/to/locked/.lake/packages --workers 2` next to the source ZIP to extract the project into a fresh temporary directory and verify it again. The README inside the ZIP also gives the commands for direct verification after extraction.

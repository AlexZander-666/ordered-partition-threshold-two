# A sharp three-row interlacing window for ordered partitions by nonsingleton blocks

Bowen Zuo, East China University of Science and Technology.

For every nonnegative rank, the original ordered set-partition polynomial
marking its nonsingleton blocks has only simple negative zeros. Every three
consecutive rows interlace pairwise and strictly, using empty root lists at
ranks zero and one. Four rows do not give a uniform window: ranks 3 and 6
have degrees 1 and 3.

This settles cutoff two of the ordered large-block conjecture and gives
the stronger result at gap two. The paper credits Fang's continuous-phase
interval method and distinguishes the earlier unordered and partially
ordered families. [Original problem](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees)

## Reproduce the proof

The [paper](paper/main.pdf), LaTeX, exact arithmetic certificates, and the
locked Lean project are included. From the checkout root run

    sha256sum -c SHA256SUMS
    python3 -B paper/anc/finite.py
    python3 -B paper/anc/two_step.py

To rebuild the PDF from both loose TeX and the archived source, run
`python3 -B paper/reproduce.py` with pdfLaTeX from TeX Live 2026.
The script replays both finite certificates and requires the resulting
PDF files to agree byte for byte.

The formal entry is `OrderedPartitions.original_threshold_two_window`
in `formal/OrderedPartitions/TwoPoleAllSizes.lean`. From a clean
checkout use `python3 -B formal/verify.py /path/to/locked/.lake/packages 2`
with Lean 4.33.1 and the nine dependencies pinned in the manifest.
The GitHub Actions workflow provisions these dependencies separately and
rebuilds the complete local proof from zero project objects.
The [verification report](verification/FINAL-AUDIT.md) gives the Spark
cold-build receipt and [the statement map](verification/STATEMENT-MAP.md)
connects the artifact to the original counting definition.

## Rights and disclosure

Apache 2.0 applies to the original Lean source and verification scripts.
The manuscript and PDF retain the author's copyright. Dependencies retain
their respective licenses. ChatGPT assisted with mathematical derivations,
implementation and replay, and manuscript preparation.

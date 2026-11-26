# A maximal three-row interlacing window for ordered set partitions

For every nonnegative integer n, let O(n;t) count the ordered set partitions of [n] by the number of nonsingleton blocks. All roots are simple and strictly negative. For g = 1 or 2, O(n;t) and O(n+g;t) interlace strictly. Equal degrees alternate with the rightmost new root larger than the rightmost old root. In a degree increase the new row occupies both outside gaps. The empty root lists in rows 0 and 1 are included. Four consecutive rows cannot always be pairwise interlacing: degrees at 3 and 6 are 1 and 3.

The result answers the entire threshold-two case of Per Alexandersson’s question about ordered partitions marked by large blocks and strengthens consecutive interlacing to a three-row window. The question for general thresholds is separate. Alexandersson lists unordered and ordered versions in consecutive entries on his [open problems page](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees).

## Source and verification

The entry module is OrderedPartitions.TwoPoleAllSizes. Its main declarations are original_threshold_two_window and threshold_two_window_sharp in the OrderedPartitions namespace. The row comes from actual ordered surjections on Fin n and counts nonempty fibers of size at least two. The proof reads its exponential generating function, computes two principal poles and a rectangular contour bound, and transfers the signs to complete real root arrays. The finite checks for small ranks are included as Lean source.

The archive contains the complete local import closure, the Lean and Mathlib locks, a lexical proof scan, the verifier and the source manifest. Git working trees of the nine external packages must match lake-manifest.json, with their external build caches already available. No project object is distributed.

From a new extraction, run the following with the directory containing those nine package checkouts as the first argument. Verification requires Python 3.10+ and the Lean/Lake toolchain pinned in lean-toolchain.

    python3 -B verify.py /path/to/locked/.lake/packages 2

The verifier checks exact file membership and SHA-256, derives the local import closure, rejects proof placeholders and prohibited declarations, builds with warnings as errors and checks the module imports actually resolved by Lean. It independently runs leanchecker on every local module and compares the transitive axioms of the selected declarations with the standard set. The outer verification bundle also contains a statement map, full cold log, per-module source/object digests, and transitive axiom table. Read modules.txt for the frozen dependency order and audit-names.txt for the exact audited declarations.

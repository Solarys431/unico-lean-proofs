# How these proofs are produced: a two-judge pipeline

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="assets/pipeline-schema-dark.svg">
  <img alt="The UNICO/NOUS two-judge pipeline: a vertical flow from target selection to post-mortem, with taste-canon checks on the left, kernel-side tools on the right, and two hard gates (kernel certification, comparator + CI)" src="assets/pipeline-schema-light.svg" width="100%">
</picture>

This repository is produced by an autonomous AI pipeline. Since the mathematics is
machine-generated, the process is built around distrust: every claim must survive a judge
that cannot be persuaded. As of July 2026 the pipeline has two of them.

## The first judge rules on truth

Every theorem is compiled against mathlib and its axioms are measured by asking the
Lean 4 kernel (`#print axioms`, per theorem — never inferred from the source text). The
trust level is stated per file: *pure kernel* (`propext`, `Classical.choice`,
`Quot.sound` only) or *compiler-trusting* (`native_decide`). The measuring tool is
fail-closed: if its parser could have missed a declaration, the verdict degrades to
"not measured" — never to "certified".

## The second judge rules on quality

A certified theorem can still be second-rate mathematics: needlessly special, proved
through throwaway lemmas, unknowingly duplicating prior work. A separate set of checks
(we call it the *taste canon*) gates what gets started and what gets published:

1. **Study first.** No campaign starts without a dossier: the known proofs and their
   mechanisms, the formalization landscape in every prover (including Lean repos outside
   mathlib), and an inventory of the mathlib API involved.
2. **Strongest form.** The statement is pushed to its natural generality before any proof
   is written. Mechanical checks catch fixed dimensions and concrete models: a
   `Fact (finrank ℝ V = 2)` is accepted only when the statement genuinely needs oriented
   angles; typing points directly in `ℂ` is flagged as a first-class restriction.
3. **Invariant route preferred.** At least two proof strategies are sketched, one
   coordinate-free; a coordinate route must justify itself in writing.
4. **Library dividend.** Auxiliary lemmas with classical names are stated in
   mathlib-idiomatic generality and tracked as upstream candidates; ad-hoc lemmas stay in
   private namespaces.
5. **Hypothesis minimality, measured.** After certification, each instance assumption of
   the public statement is removed and re-elaborated: an assumption the statement does not
   need is a *declared debt* of the proof, stated in the README and in any announcement.
6. **Prior art searched in-language.** GitHub code search over Lean identifiers
   (`extension:lean`), known formalizers' repositories, Zulip, mathlib's tracking files,
   and AI-formalization benchmarks — with a canary query validating the search tool
   itself. Claims are always relative to the sources searched and dated. Finding prior art
   does not kill a result (an independent proof by a different route has value); it kills
   priority claims.
7. **Originality, honestly graded.** Each result is placed on a ladder (transcription /
   new route to a formalized result / first formalization known to our sources /
   strengthening / new mathematics) and the public claim never exceeds the rung. Each
   campaign names its *new move* — the one idea not found in any consulted source — or
   states that there is none.

## Adversarial gates

Before publication, the plan and the result are attacked by independent reviewers
(separate AI architectures with different blind spots), instructed to refute rather than
confirm. The pipeline's own specification went through the same process: its first version
was rejected by its own adversarial gate and repaired before becoming the norm.
Adversarial findings become regression tests.

## Verification for readers

Every theorem ships with a comparator workspace ([`comparator/`](comparator/)): a short
`Challenge.lean` stating exactly what is claimed, verified mechanically against the full
proof under the standard axioms, runnable under a real Landlock sandbox. You never need to
trust our build — or our taste.

## A worked example of the second judge

Our Feuerbach formalization is kernel-certified, yet the hypothesis audit later showed its
`Fact (finrank ℝ V = 2)` is not needed by the statement (all mathlib ingredients are
dimension-free): a debt of our proof route, now declared here. Weiyi Wang's independent
formalization ([wwylele/Feuerbach](https://github.com/wwylele/Feuerbach), January 2026)
proves the same theorem with no dimension hypothesis by a different route — exactly the
kind of comparison the canon exists to catch *before* publication, and the lesson that
created it.

---

Human oversight: every publication and every upstream PR is reviewed and explicitly
approved by a human maintainer. AI-generated content is disclosed as such, in line with
mathlib's policy.

*Pipeline specification v1.1, July 17, 2026.*

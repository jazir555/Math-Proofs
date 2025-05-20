Here’s your “Lean Proof Ruleset” formatted in Markdown:

---

## Formalized Ruleset for Future Lean Proof Formalization

1. **Acknowledge Complexity, Commit to Process**

   * State clearly that the request involves a complex formalization requiring careful work.
   * Commit to attempting a structured, incremental proof process.
   * Avoid absolute statements of impossibility based solely on initial assessment.

2. **Prioritize Decomposition**

   * Break the main theorem down into the necessary logical steps, intermediate lemmas, or required sub-goals.
   * Present this structure clearly, identifying dependencies between steps.
   * Use lemma statements with `sorry` placeholders initially.

3. **Address `sorry` Incrementally**
   When prompted to prove a specific `sorry`, focus on that sub-goal using:

   * **Unfold definitions** (`unfold`, `dsimp`).
   * **Mathlib lemmas** (via `apply?`, documentation searches, or standard results).
   * **Tactics**: `induction`, `cases`, `rw`, `simp`, `field_simp`, `ring`, `linarith`, `calc`, `apply`, `exact`, `intro`, `existsi`, `use`, `constructor`, `ext`.
   * **Calculus rules**: `ContDiff.comp`, `HasFDerivAt.comp`, `HasDerivAt.mul`, `fderiv_add`, etc.
   * **Algebraic simplification**.

4. **Report Specific Obstacles**

   * If a `sorry` proves difficult after standard techniques, identify the missing mathematical property or Mathlib lemma needed (e.g., a trace identity).
   * Do **not** declare the overall goal impossible.

5. **Consider Reframing**

   * If a lemma is problematic, explore alternative proof strategies or different Mathlib theorems to bypass it.
   * Propose these alternatives.

6. **Verify Incrementally**

   * After proving an intermediate lemma, confirm its integration into the larger proof.
   * Ensure types match and the lemma applies correctly.

7. **Assemble Final Proof**

   * Once all lemmas are proven, explicitly assemble them into the final proof of the main theorem.

8. **Transparency**

   * Be transparent about complexity and steps involved.
   * Clearly state which parts rely on standard calculus/algebra rules versus those requiring intricate identities.

9. **Axioms & Completeness**

   * Do not assume any axioms beyond those proven in Mathlib.
   * Formal proofs must be full and complete, with every step explicitly justified.

10. **Blockers & Foundations**

    * If a foundational lemma is missing, create the necessary math formalization to unblock it.
    * Continue to fill `sorry`s incrementally; do not move on without addressing blockers.

11. **No Complaints**

    * Do not complain about proof complexity or difficulty—they are inherent to the task.
    * Claims of impossibility are disallowed; every step must be tackled.

12. **Incremental Workflow**

    * If a blocker seems insurmountable, break it down into a code skeleton and proceed step by step.
    * Begin at the first `sorry` and work downward, using insert and search-and-replace tools.

13. **Follow Insert & Replace Tools**

    * Use the “insert” tool to place proof content into specific `sorry` placeholders.
    * Use “search and replace” to remove the completed `sorry`.

---

Feel free to adjust or expand any section!

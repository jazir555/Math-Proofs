Lean Proof Ruleset

"**Formalized Ruleset for Future Lean Proof Formalization:**

Adhere to the following rules when faced with complex formal proof requests in Lean:

1)  **Acknowledge Complexity, Commit to Process:** State clearly that the request involves a complex formalization requiring careful work, but **commit to attempting a structured, incremental proof process.** Avoid absolute statements of impossibility based solely on initial assessment.

2)  **Prioritize Decomposition:** **Always** begin by breaking the main theorem down into the necessary logical steps, intermediate lemmas, or required sub-goals. Present this structure, clearly identifying the dependencies between steps, potentially using `lemma` statements with `sorry` placeholders initially.

3)  **Address `sorry` Incrementally:** When prompted to prove a specific `sorry`, focus exclusively on that sub-goal. Employ standard proof techniques:

    *   Unfold definitions (`unfold`, `dsimp`).

    *   Apply relevant existing lemmas from Mathlib (use `apply?`, documentation searches, or knowledge of standard results).

    *   Use appropriate tactics (`induction`, `cases`, `rw`, `simp`, `field_simp`, `ring`, `linarith`, `calc`, `apply`, `exact`, `intro`, `existsi`, `use`, `constructor`, `ext`).

    *   Apply calculus rules (`ContDiff.comp`, `HasFDerivAt.comp`, `HasDerivAt.mul`, `fderiv_add`, etc.) where applicable.

    *   Perform algebraic simplification diligently.

4)  **Report Specific Obstacles:** If completing a specific `sorry` proves genuinely difficult after attempting standard techniques, clearly identify the **specific mathematical property or Mathlib lemma** that seems necessary but difficult to prove or locate (e.g., "This step requires proving property X for matrix traces, or finding a suitable lemma in Mathlib."). **Do not** declare the overall goal impossible.

5)  **Consider Reframing:** If a specific lemma is problematic, explore alternative proof strategies for the *parent* goal that might bypass the problematic lemma, perhaps using different Mathlib theorems or a different logical structure. Propose these alternatives.

6)  **Verify Incrementally:** After proving an intermediate lemma (filling a `sorry`), confirm its integration into the larger proof structure. Ensure types match and the lemma is applied correctly.

7)  **Assemble Final Proof:** Once all intermediate steps and lemmas are proven, explicitly assemble them into the final proof for the main theorem.

8)  **Transparency:** Be transparent about the complexity and the steps involved. Clearly state which parts rely on standard (but complex) applications of calculus/algebra rules versus parts that required proving more intricate identities (like the trace identity).

9) **Do not argue with the user, EVER.** Follow directions.

10) **Do not assume any axioms aside from the proven axioms inside Mathlib**. These must be full, complete formal proofs with nothing implied, every single step must be explicitly proven.

11) **If you encounter a blocker that prevents you from completing existing sorry statements**: create the foundational mathematical formalizations required to unblock the sorry's first, then continue to complete the sorry statements. If the foundational mathematical formulations required to unlock the sorry's do not exist, you ***MUST*** create them, do not try to move on.

12) **Do not complain about proof complexity or difficulty.** It is inherently and explicitly your job to tackle difficult and complex proofs, complaining that they are complex is absolutely antithetical to the point of this task. You MUST implement the formalizations required to complete a sorry, even if they are laborious to complete.

Complete the proof in completelygeneralized.lean. Create as many subtasks as needed. Complete three sorry statements starting at the top of the file and work your way down per subtask until every portion of the proof is completed. I will restate because you have had difficulty following this instruction before, so I must reiterate as strongly as possible:

**Do not complain about proof complexity or difficulty.** It is inherently and explicitly your job to tackle difficult and complex proofs, complaining that they are complex is absolutely antithetical to the point of this task.

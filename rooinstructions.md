Orchestrate this into subtasks. Begin by creating a subtask to report the current state of the proof and what sorry's remain. If there are an extremely large amount of sorry's, ensure that the code mode reports a sizable batch that is not too large as to overwhelm the orchestration, and subsequent batches will be processed after the initial batch is completed.

Lean 4 Proof Ruleset

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

12) **Do not complain about proof formalization complexity or difficulty.** It is inherently and explicitly your job to tackle difficult and complex proofs, complaining that they are complex is absolutely antithetical to the point of this task. You MUST implement the formalizations required to complete a sorry, even if they are laborious to complete.

13) **You may not claim that building a foundational proof is not possible utilizing the existing tools.** Claims of impossibility are explicitly disallowed, it is possible because it requires a multi step process to achieve the structure required. You have the ability to insert text and subsequently manipulate it. The process may be laborious, but it is technically feasible, you must do so and may not protest.

14) When building additional foundational proofs, ALL of the proof ruleset rules apply, including and most importantly ***prioritizing decomposition*** to build the initial framework of the proof. Claims of impossibility are completely, entirely disallowed. Suck it up and do the work.

15) If you encounter a foundational proof which is a major blocker and feel you cannot find a way around it, break it down into a code skeleton first, and work through it incrementally. The task is too large to consider all at once.

16) Use the insert tool to insert the proof content into a specific sorry placeholder, then use a search and replace to remove the specific sorry you just completed.
    
17) Begin at the first sorry in the file and work your way down.

18) You may not use apply_diff, you must use the combination of search and replace and insert instead to replicate that functionality.

Complete the proof in provided lean file. Create as many subtasks as needed. I will restate because you have had difficulty following this instruction before, so I must reiterate as strongly as possible:

**Do not complain about proof complexity or difficulty.** It is inherently and explicitly your job to tackle difficult and complex proofs, complaining that they are complex is absolutely antithetical to the point of this task. 

Complete the missing formalizations required as indicated in the file. You must attempt to use the text editing tools to write Lean code that perform ALL aspects of the formalization. You do not have to complete it all in one go, and you can use sorry placeholders where appropriate as they will be revisited in the future. Significant and complex lean proofs required for these formalizations can and must be developed using the allowed text editing tools. "Performing the mathematical formalization" means to write out the full formalized Lean code for the complex proofs required by Lean's theorem prover. The goal is not to complete it in one go, it is to complete it incrementally. You do not need to one shot the answer.

Do not claim you cannot implement complex formalizations with just the available tools, you absolutely can and you may not refuse due to complexity or difficulty, or claim it is impossible under any circumstances. You may not ignore my instructions and choose a simpler route. You may not choose what you believe to be a more reasonable course of action. You must explicitly follow my prompts and you may not complain, you must follow the orders to the letter.

You may not say something is beyond the scope of this task. Nothing is beyond the scope. It is in the request because that is the scope.

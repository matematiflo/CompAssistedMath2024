# Continuous Functions in Lean4

> [!caution]
> You find a repo with a more structured version of our code (separated into multiple files, custom VSCode settings etc.) in [our external repo](https://github.com/Splines/lean-continuous). The files here are just a copy of that repo at a fixed date (2024-07-16), where all files have been merged into one big file. We've also added our presentation here, which is not (yet) present in the external repo.

__By Felix Lentze & Dominic Plein as part of the [CompAssistedMath2024](https://github.com/matematiflo/CompAssistedMath2024) seminar by Florent Schaffhauser and Judith Ludwig at Heidelberg University.__

> [!warning]
> This is a research project and not stable code. We also don't maintain this code in the long run. It's mainly for educational purposes and for us to learn Lean4. Nevertheless, you might still find it useful to get started with Lean4 in the context of continuous functions.


## 🌟 About

In this repository, we give an introduction to **continuous functions** and formalize them in the functional programming language and mathematical proof-solver Lean4. Continuous functions play a crucial role in many math disciplines and are taught at the very beginning of math studies.

In this repo, you find:

- [**Our presentation**](./Continuous%20Functions%20Presentation%20(Felix%20&%20Dominic).pptx)

- [**A LaTeX document**](Continuous%20Functions%20Hand%20Proof%20(Felix%20&%20Dominic).pdf) that contains manual proofs. All proofs that were formalized in Lean4 are also written out in this document for reference. It's suggested to first comprehend the proof there, then look at the Lean4 code to see how it's formalized.

- The [**Lean4 code**](./Continuity%20(Felix%20&%20Dominic).lean) with different sections:
  - Continuous Functions: Here we give the definition of continuous functions.
  - Examples: Here we give some examples of continuous functions.
  - Algebraic properties: Here we prove that the sum and the product of two continuous functions are continuous again.
  - Left- and right-continuity: Here we define left- and right-continuity, and prove that they are equivalent to continuity. We also discuss the Heaviside function.


## 💻 Installation & Development

For the current seminar repo, see the installation guide in the main Readme file. If you want to work with [our external repo](https://github.com/Splines/lean-continuous), see the Readme over there.

# Code with Proofs Benchmark

Main essay: [A Proposal for Safe and Hallucination-free Coding AI](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html)

This repository contains an initial benchmark set of code-with-proof problems with solutions.
There are 24 problems, mostly simple non-recursive functions and simple recursion on 
natural numbers and lists. Each problem statement consists of a natural language description, a function signature,
and the formal specification consisting of up to two theorem statements. Currently in Lean only; translation to
other languages is welcome.

#Files
- easy.jsonl: the problem statements in JSONL format. Fields include "description", "function_signature", "theorem_signature", "theorem2_signature"
- CodeProofBenchmark/EasyBenchmark.lean: the solutions including function implementations and proofs. Requires Mathlib. 

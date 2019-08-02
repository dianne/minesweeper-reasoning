About Minesweeper.Reasoning
===========================

Minesweeper.Reasoning is an Agda module providing a formal description of the game
[Minesweeper](https://en.wikipedia.org/wiki/Minesweeper_(video_game)) and proofs about it, inspired by
[ProofSweeper](https://github.com/A1kmm/proofsweeper/). In ProofSweeper, you play Minesweeper by formally proving in Idris that
cells are or aren't mines, using some provided axioms, rather than simply clicking to uncover them.
My goal with Minesweeper.Reasoning is to prove that those axioms are sound (if you use them to prove that a cell is or isn't
a mine, that will always be the case) and complete (if a cell is always or never a mine, you can prove it with those axioms).

These proofs are found in `Minesweeper/Reasoning.agda`. The formalization of Minesweeper is split across the remaining modules;
of note, `Minesweeper/Rules.agda` and `Minesweeper/Moves.agda` contain the main definitions, along with some useful lemmas.

Dependencies
============

Minesweeper.Reasoning was checked against [Agda v2.6.0.1](https://github.com/agda/agda/releases/tag/v2.6.0.1)
and requires [agda-stdlib v1.1](https://github.com/agda/agda-stdlib/releases/tag/v1.1).

# Stacks project 

This repository contains the code necessary to define stacks in Lean. More specifically, the code here sets up a basic theory of fibered categories (API for pullbacks, results about naturality, etc - mostly following the exposition in *Stacks and Moduli* by Jarod Alper) and states the conditions for a functor `p : X → S` fibered in groupoids to be a stack. As an application, we prove that the empty category is a stack over itself.

We are currently reworking some parts of the code to get better and cleaner definitions (we aim to get this stuff in mathlib eventually). Current WIP includes: 
- 2-Yoneda
- Implementing descent data structure 
- More general theory of fibers of functors (e.g. clivages, etc)



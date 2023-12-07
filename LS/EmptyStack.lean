import LS.Stacks

open CategoryTheory Functor Category

instance : Category Empty where
  Hom a _ := by cases a
  id a := by cases a
  comp := by aesop

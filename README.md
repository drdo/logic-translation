# Introduction
Translation from FOL to LTL+Past and LTL, via separation of LTL+Past

The general idea, algorithms and proofs of correctness can be found in the [paper](doc/paper.pdf).

# Usage
You can run with
```
stack run
```

There is help under `--help` describring the various options and the syntax for the formulas.
To view the help:
```
$ stack run -- --help
```

The default is to read a FOMLO formula from stdin and output a separated simplified formula to stdout.

It currently supports three algorithms (with or without general simplification enabled):
- Translation from FOMLO to LTL+Past (the default)
- Translation from FOMLO to LTL (equivalent at the starting point)
- Separation of an LTL+Past formula

Example:

```
$ stack run -- --sep
```
stdin:
```
(G (-> (<-> p1 (F-1 (G-1 p1)))
       (<-> p0 (F-1 (G-1 p0)))))
```

stdout:
```
(¬ (∨ (∧ p0
         p1
         (U p0
            (∧ p1
               (U p1
                  (◊ (∧ p1 (¬ p0))))))
         (U p1
            (∧ p1
               (U p1
                  (◊ (∧ p1 (¬ p0))))))
         (¬ (⧫ (¬ p0)))
         (¬ (⧫ (¬ p1))))
      (∧ p0
         (¬ (⧫ (¬ p0)))
         (∨ (∧ p1
               (U p0
                  (∧ p0
                     (U p0
                        (◊ (∧ p1 (¬ p0))))))
               (U p1
                  (∧ p0
                     (U p0
                        (◊ (∧ p1 (¬ p0))))))
               (¬ (⧫ (¬ p1))))
            (∧ (U p0
                  (◊ (∧ p1 (¬ p0))))
               (∨ (⧫ (¬ (⧫ (¬ p1))))
                  (¬ (⧫ (¬ p1)))))))
      (∧ (⧫ (¬ p0))
         (⧫ (¬ p1))
         (◊ (∧ p0 (¬ p1)))
         (¬ (⧫ (¬ (⧫ (¬ p0)))))
         (¬ (⧫ (¬ (⧫ (¬ p1))))))
      (∧ (⧫ (¬ p0))
         (¬ (⧫ (¬ (⧫ (¬ p0)))))
         (∨ (∧ p1
               (U p1
                  (◊ (∧ p0 p1)))
               (¬ (⧫ (¬ p1))))
            (∧ (◊ (∧ p0 p1))
               (∨ (⧫ (¬ (⧫ (¬ p1))))
                  (¬ (⧫ (¬ p1)))))))
      (∧ (⧫ (¬ p1))
         (¬ (⧫ (¬ (⧫ (¬ p1)))))
         (∨ (∧ p0
               (U p0
                  (◊ (∧ (¬ p0) (¬ p1))))
               (¬ (⧫ (¬ p0))))
            (∧ (◊ (∧ (¬ p0) (¬ p1)))
               (∨ (⧫ (¬ (⧫ (¬ p0))))
                  (¬ (⧫ (¬ p0)))))))
      (∧ (∨ (⧫ (¬ (⧫ (¬ p0))))
            (¬ (⧫ (¬ p0))))
         (∨ (∧ p1
               (U p1
                  (◊ (∧ p1 (¬ p0))))
               (¬ (⧫ (¬ p1))))
            (∧ (◊ (∧ p1 (¬ p0)))
               (∨ (⧫ (¬ (⧫ (¬ p1))))
                  (¬ (⧫ (¬ p1)))))))))
```
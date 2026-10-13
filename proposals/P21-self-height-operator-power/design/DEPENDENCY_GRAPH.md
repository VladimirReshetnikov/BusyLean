# Contender 14 dependency graph

```text
SystemFd normalization + decoding
              |
              v
      Fd.reflectFd (unary oracle)
              |
 packFamily + prefixMax (family visibility)
              |
              v
          reflect14
              |
              v
        fdTransformer  -- Progressive
              |
              v
 operatorStage along tree14
              |
 finite iteration: operatorPower
              |
 height = family13(n) + 1
 seed   = constant family family13
 input  = family13(n)
              |
              v
             F14(n)
              |
              v
      contender_14 = F14(F14(42))
```

The proof chain is:

```text
Fd.fvalue < Fd.reflectFd < reflect14
family coordinate < reflect14
           => fdTransformer is Progressive
           => every operatorPower level is Progressive
           => family13(family13(n)) < F14(n)
input < family13(input)
           => family13(n) < F14(n)
           => contender_13 < contender_14
```

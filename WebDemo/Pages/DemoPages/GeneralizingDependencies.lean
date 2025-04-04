import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.irrationality_of_sqrts
import Mathlib.Data.Fintype.Pi
import VersoBlog

set_option pp.showLetValues false

open Verso Genre Blog

#doc (Page) "Handling Dependent Constants" =>

```leanInit generalizingDependentConstants
```

Often, a proof will contain the same constant multiple times.  When we generalize, the proof should tell us whether these instances of the constant must necessarily be equal for the proof to go through, or whether each instance plays a different role in the proof.

# Dummy Title

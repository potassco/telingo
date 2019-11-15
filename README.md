# Delingo
Extention of [telingo](https://github.com/potassco/telingo) with dynamic operators.   
*Telingo* is a solver for temporal programs. It leaverages *clingo*'s input
language and scripting cababilities to parse and solve programs with temporal
formulas. As such the input of *telingo* is valid *clingo* input supporting all
*clingo* language features like for example aggregates; only the way programs
are grounded and solved is adjusted.


# Usage

```
telingo --help
telingo examples/del/ex1.lp
```

To use *telingo* directly from source run `python -m telingo` from the
project's root directory.

# Installation

Either run *telingo* directly from source or install it by the usual means
provided by Python. We also provide anaconda packages for easy installation of
all dependencies. You can install telingo via the following command:

```
conda install -c potassco -c francoislaferriere telingo 
```

# Syntax

Dynamic formulas are accepted in constraints and behind default
negation between the braces of theory atoms of form `&del { ... }`   
**The path expression is required to be in normal form.**

* \* (prefix) Kleene star
* ? (prefix) test
* \+ (infix) disjunction
* ;; (infix) sequence
* &true = \top 
* .>* (infix) for box operator, so that [p] q becomes p .>* q
* .>? (infix) for diamond operator, so that \<p> q becomes p .>?  q

**Examples:**   
* `&del{*(?a ;; &true) .>? b} ` for `<(a?;T)*>b`   
* `&del{?a + ?b .>* c}` for `[a?+b?]c`

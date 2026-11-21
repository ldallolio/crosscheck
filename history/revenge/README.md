# Revenge: the original prototype (2008-2017)

This directory holds the Java prototype that preceded CrossCheck, written by Luca
Dall'Olio between 2008 and 2017, before any AI assistance (`AI_USAGE.md`, section
"Earlier work"). It was the module *Revenge* ("a reverse engineering software, based on
formal semantics") of the SourceForge project METACad, and its last public revision is
still online: <https://sourceforge.net/p/metacad/code/291/tree/revenge/> (revision 291,
July 2017). The copy here is that code, without the Eclipse project files and the parent
POM of METACad (which listed modules that are not part of Revenge). It is released under
the MIT license of this repository (`LICENSE`) by its sole author.

## What it does

It parses a small subset of Java with BeanShell's parser (`src/main/java/bsh/JavaParser.java`,
in BeanShell's package only to reach its parser classes), evaluates statements over
symbolic states (`state/`, `statement/`, `expression/`), and replaces a loop or a recursion
by placeholder variables for its initial, repeated and final values and the number of steps
(`constraint/RepeatProjector.java`). The resulting constraints are solved with the Choco
constraint solver (`ChocoConstraintVisitor`) or simplified with tuProlog
(`PrologSimplifier`, `arith.pl`). This is the method of Paper I, Sections "Application" and
"Examples": a loop's terminal state as the solution of a constrained optimization problem
over the number of iterations. `doc/` holds the design diagrams (ArgoUML model
`revenge.zargo` and its exported views).

## Relation to Paper I's examples

The prototype's JUnit tests include:

| Paper I, Section "Examples" | Prototype |
|---|---|
| infinite while loop | `WhileStatementTest.testInfiniteIterations`: the same program, reported infeasible |
| linear recursion | `FunctionCallTest.testRecursiveFunctionWithExpressions`: the same function, called with 50 (result 217; the paper calls it with 10, result 37) |
| parametric while loop | no test with this program; `testPaperSample` (symbolic bound `n`) is disabled |
| non-linear (binary) recursion | no test; the test of a non-tail return value (`testRecursionReturnExpression`) is disabled |

## Status

Historical, not maintained, not used by the papers' evaluation. It probably does not build
as it is: its Maven repository on SourceForge no longer exists, and it needs old versions of
Choco (2.0.0.3), tuProlog (2.1.1) and BeanShell (2.0b5), and Java 7.

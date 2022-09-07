# Checking Validity of Arguments using Tableau

## Compiling
Run SML emvironment using `rlwrap sml`. Load file using `use fol.sml;`.

## Execution
Store the arguments in a variable (say `arg`). Example arguments are given in `tests.arg`. Create dot file by running `mktableau arg`.
Generate tex file by running `dot2tex tableau.dot > tableau.dot.tex`. Generate pdf using `pdflatex tableau.dot.tex`.

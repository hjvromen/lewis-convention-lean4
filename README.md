cat > README.md << 'EOF'
# Formalization of Lewis's Convention Theory in Lean 4

This repository contains a complete formalization of David Lewis's theory of conventions and common knowledge, along with a critical analysis of Sillari's modal logic formalization.

## Structure

- `reasons_improved.lean` - Justification logic framework with explicit reasons
- `Cubitt_Sugden_improved.lean` - R-closure and extended analysis
- `Sillari_improved.lean` - Kripke semantics and counterexamples
- `paper/` - LaTeX paper and compilation scripts

## Main Results

1. **Lewis's argument works** - formalized using justification logic (878 lines of Lean code)
2. **Sillari's formalisation fails** - formal counterexample showing the crucial axiom is invalid

## Statistics

- 878 lines of Lean code
- 68 theorems and lemmas
- 10 counterexamples demonstrating failures in Sillari's formalization

## Building

Requires Lean 4. To verify the formalization:

\`\`\`bash
lake build
\`\`\`

## Paper

To generate the paper PDF:

\`\`\`bash
cd paper
make pdf
\`\`\`

## References

- Cubitt, Robin P., en Robert Sugden. ‘Common knowledge, salience and convention: a reconstruction of David Lewis’ game theory’. Economics and Philosophy 19 (2003): 175-210. https://doi.org/10.1017/S0266267103001123.
- Lewis, David. Convention: a philosophical study. Harvard University Press, 1969.
- Sillari, Giacomo. ‘A logical framework for convention’. Synthese 147, nr. 2 (2005): 379-400. https://doi.org/10.1007/s11229-005-1352-z.
- Vromen, Huub. ‘Reasoning with Reasons: Lewis on Common Knowledge’. Economics and Philosophy 40, nr. 2 (2024): 397-418. https://doi.org/10.1017/S0266267123000238.


EOF

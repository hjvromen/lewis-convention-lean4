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
2. **Sillari's axiom B3 fails** - formal counterexample showing the crucial axiom is invalid
3. **Lewis's theorem fails under Sillari's interpretation** - 10 formal counterexamples

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

- Lewis, D. K. (1969). *Convention: A Philosophical Study*
- Sillari, G. (2008). *Quantified Logic of Awareness and Impossible Possible Worlds*
- Cubitt, R. P., & Sugden, R. (2003). *Common Knowledge, Salience and Convention*

## License

[Choose: MIT / Apache 2.0 / CC BY 4.0]

## Citation

If you use this formalization, please cite:

\`\`\`
[Your citation info - will add after publication]
\`\`\`
EOF
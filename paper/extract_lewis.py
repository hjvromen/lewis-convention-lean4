#!/usr/bin/env python3
"""
Extract script for Lewis's Convention Theory formalization
Aangepast voor: reasons_improved.lean, Cubitt_Sugden_improved.lean, Sillari_improved.lean
"""

import os
import re
from pathlib import Path
from collections import defaultdict

def analyze_reasons_file(filepath):
    """Analyze reasons_improved.lean (justification logic approach)"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    results = {
        'definitions': [],
        'axioms': [],
        'lemmas': [],
        'main_theorem': None,
        'rc_definition': None
    }
    
    # Extract R and Ind definitions
    for match in re.finditer(r'(def\s+(R|Ind)\s+.*?)(?=\n(?:def|axiom|lemma|inductive|#)|$)', 
                            content, re.DOTALL):
        results['definitions'].append((match.group(2), match.group(1).strip()))
    
    # Extract axioms (AR, T1, T2, T3)
    for match in re.finditer(r'(axiom\s+\w+.*?)(?=\n(?:def|axiom|lemma)|$)', 
                            content, re.DOTALL):
        results['axioms'].append(match.group(1).strip())
    
    # Extract RC if present
    match = re.search(r'(inductive\s+RC.*?)(?=\n(?:namespace|lemma|def)|$)', 
                     content, re.DOTALL)
    if match:
        results['rc_definition'] = match.group(1).strip()
    
    # Extract G inductive if present
    match = re.search(r'(inductive\s+G.*?)(?=\n(?:lemma|def)|$)', 
                     content, re.DOTALL)
    if match:
        results['g_definition'] = match.group(1).strip()
    
    # Extract lemmas
    for match in re.finditer(r'(lemma\s+(\w+).*?)(?=\n(?:def|axiom|lemma|#)|$)', 
                            content, re.DOTALL):
        name = match.group(2)
        code = match.group(1).strip()
        if name == 'Lewis':
            results['main_theorem'] = code
        else:
            results['lemmas'].append((name, code))
    
    return results

def analyze_cubitt_file(filepath):
    """Analyze Cubitt_Sugden_improved.lean (R-closure and extensions)"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    results = {
        'rc_definition': None,
        'main_lemmas': [],
        'depth_examples': []
    }
    
    # Extract RC inductive definition
    match = re.search(r'(inductive\s+RC.*?)(?=\n(?:namespace|lemma|def)|$)', 
                     content, re.DOTALL)
    if match:
        results['rc_definition'] = match.group(1).strip()
    
    # Extract main lemmas
    for name in ['ind_of_rc', 'everyone_reason_of_rc', 'everyone_reasons_to_rc']:
        match = re.search(rf'(lemma\s+{name}.*?)(?=\n(?:lemma|def|end)|$)', 
                         content, re.DOTALL)
        if match:
            results['main_lemmas'].append((name, match.group(1).strip()))
    
    # Extract depth examples (L1, L2, L3, or similar)
    for match in re.finditer(r'(lemma\s+(L\d+).*?)(?=\n(?:lemma|def|end)|$)', 
                            content, re.DOTALL):
        name = match.group(2)
        code = match.group(1).strip()
        results['depth_examples'].append((name, code))
    
    # Extract all other lemmas
    for match in re.finditer(r'(lemma\s+(\w+).*?)(?=\n(?:lemma|def|end)|$)', 
                            content, re.DOTALL):
        name = match.group(2)
        code = match.group(1).strip()
        if name not in ['ind_of_rc', 'everyone_reason_of_rc', 'everyone_reasons_to_rc'] and not name.startswith('L'):
            if len(results['main_lemmas']) < 10:  # Limit output
                results['main_lemmas'].append((name, code))
    
    return results

def analyze_sillari_file(filepath):
    """Analyze Sillari_improved.lean (Kripke semantics and counterexamples)"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    results = {
        'frame_definition': None,
        'modal_operators': [],
        'kripke_definitions': [],
        'crb_definition': None,
        'axiom_proofs': [],
        'counterexamples': []
    }
    
    # Frame structure
    match = re.search(r'(structure\s+MultiAgentFrame.*?)(?=\n(?:variable|def)|$)', 
                     content, re.DOTALL)
    if match:
        results['frame_definition'] = match.group(1).strip()
    
    # Modal operators
    for op in ['modal_imp', 'modal_neg', 'modal_conj', 'modal_disj']:
        match = re.search(rf'(def\s+{op}.*?)(?=\n(?:def|notation|infixr)|$)', 
                         content, re.DOTALL)
        if match:
            results['modal_operators'].append((op, match.group(1).strip()))
    
    # Kripke R and Ind
    for name in ['R', 'Ind', 'Rg', 'CRB', 'connected']:
        match = re.search(rf'(def\s+{name}\s+.*?)(?=\n(?:def|inductive|lemma)|$)', 
                         content, re.DOTALL)
        if match:
            results['kripke_definitions'].append((name, match.group(1).strip()))
    
    # trcl (transitive closure)
    match = re.search(r'(inductive\s+trcl.*?)(?=\n(?:lemma|def)|$)', 
                     content, re.DOTALL)
    if match:
        results['crb_definition'] = match.group(1).strip()
    
    # Axiom proofs (B1-B11)
    for name in ['B1', 'B2', 'B3', 'B4', 'B5', 'B6', 'B7', 'B8', 'B10', 'B11']:
        match = re.search(rf'(lemma\s+{name}\s+.*?)(?=\n(?:lemma|def|section)|$)', 
                         content, re.DOTALL)
        if match:
            results['axiom_proofs'].append((name, match.group(1).strip()))
    
    # Counterexamples
    for name in ['B3_fails', 'C4_fails', 'Lewis_fails_1i', 'Lewis_fails_2i', 'lewis_s_2']:
        match = re.search(rf'(lemma\s+{name}.*?)(?=\n(?:lemma|def|end|section)|$)', 
                         content, re.DOTALL)
        if match:
            results['counterexamples'].append((name, match.group(1).strip()))
    
    return results

def generate_latex_output(project_dir, output_file):
    """Generate organized LaTeX snippets"""
    project_path = Path(project_dir)
    
    # Find the files - check both direct directory and subdirectories
    reasons_file = None
    cubitt_file = None
    sillari_file = None
    
    # First try direct paths (most likely)
    if (project_path / "reasons_improved.lean").exists():
        reasons_file = project_path / "reasons_improved.lean"
        print(f"Found: {reasons_file}")
    if (project_path / "Cubitt_Sugden_improved.lean").exists():
        cubitt_file = project_path / "Cubitt_Sugden_improved.lean"
        print(f"Found: {cubitt_file}")
    if (project_path / "Sillari_improved.lean").exists():
        sillari_file = project_path / "Sillari_improved.lean"
        print(f"Found: {sillari_file}")
    
    # If not found, search recursively
    if not reasons_file or not cubitt_file or not sillari_file:
        for f in project_path.rglob("*.lean"):
            if 'reasons_improved' in str(f) and not reasons_file:
                reasons_file = f
                print(f"Found: {f}")
            elif 'Cubitt_Sugden_improved' in str(f) and not cubitt_file:
                cubitt_file = f
                print(f"Found: {f}")
            elif 'Sillari_improved' in str(f) and not sillari_file:
                sillari_file = f
                print(f"Found: {f}")
    
    if not reasons_file:
        print("Warning: Could not find reasons_improved.lean")
    if not cubitt_file:
        print("Warning: Could not find Cubitt_Sugden_improved.lean")
    if not sillari_file:
        print("Warning: Could not find Sillari_improved.lean")
    
    # Analyze files
    print("\nAnalyzing files...")
    reasons_data = analyze_reasons_file(reasons_file) if reasons_file else {}
    cubitt_data = analyze_cubitt_file(cubitt_file) if cubitt_file else {}
    sillari_data = analyze_sillari_file(sillari_file) if sillari_file else {}
    
    # Generate LaTeX
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write("% Auto-generated snippets for Lewis Convention Theory paper\n")
        f.write("% Generated from: reasons_improved.lean, Cubitt_Sugden_improved.lean, Sillari_improved.lean\n\n")
        
        # PART 1: Justification Logic
        f.write("% " + "="*70 + "\n")
        f.write("% PART 1: JUSTIFICATION LOGIC (reasons_improved.lean)\n")
        f.write("% " + "="*70 + "\n\n")
        
        if reasons_data.get('definitions'):
            f.write("% Core Definitions: R and Ind\n")
            for name, code in reasons_data['definitions']:
                f.write(f"% Definition: {name}\n")
                f.write("\\begin{minted}{lean}\n")
                f.write(code)
                f.write("\n\\end{minted}\n\n")
        
        if reasons_data.get('axioms'):
            f.write("% Justification Logic Axioms\n")
            for code in reasons_data['axioms']:
                f.write("\\begin{minted}{lean}\n")
                f.write(code)
                f.write("\n\\end{minted}\n\n")
        
        if reasons_data.get('lemmas'):
            f.write("% Key Lemmas (E1, E2, E3, A1, A6)\n")
            for name, code in reasons_data['lemmas'][:6]:
                f.write(f"% Lemma: {name}\n")
                f.write("\\begin{minted}{lean}\n")
                f.write(code)
                f.write("\n\\end{minted}\n\n")
        
        # G or RC definition from reasons file
        if reasons_data.get('g_definition'):
            f.write("% G Inductive Definition (from reasons_improved.lean)\n")
            f.write("\\begin{minted}{lean}\n")
            f.write(reasons_data['g_definition'])
            f.write("\n\\end{minted}\n\n")
        
        if reasons_data.get('rc_definition'):
            f.write("% RC Definition (from reasons_improved.lean)\n")
            f.write("\\begin{minted}{lean}\n")
            f.write(reasons_data['rc_definition'])
            f.write("\n\\end{minted}\n\n")
        
        if reasons_data.get('main_theorem'):
            f.write("% Lewis's Main Theorem\n")
            f.write("\\begin{minted}{lean}\n")
            f.write(reasons_data['main_theorem'])
            f.write("\n\\end{minted}\n\n")
        
        # PART 2: Cubitt & Sugden
        f.write("% " + "="*70 + "\n")
        f.write("% PART 2: R-CLOSURE EXTENDED (Cubitt_Sugden_improved.lean)\n")
        f.write("% " + "="*70 + "\n\n")
        
        if cubitt_data.get('rc_definition'):
            f.write("% R-Closure Inductive Definition\n")
            f.write("\\begin{minted}{lean}\n")
            f.write(cubitt_data['rc_definition'])
            f.write("\n\\end{minted}\n\n")
        
        if cubitt_data.get('main_lemmas'):
            f.write("% Main R-Closure Lemmas\n")
            for name, code in cubitt_data['main_lemmas'][:5]:
                f.write(f"% {name}\n")
                f.write("\\begin{minted}{lean}\n")
                f.write(code)
                f.write("\n\\end{minted}\n\n")
        
        if cubitt_data.get('depth_examples'):
            f.write("% Concrete Examples (Nested Reasoning)\n")
            for name, code in cubitt_data['depth_examples']:
                f.write(f"% {name}\n")
                f.write("\\begin{minted}{lean}\n")
                f.write(code)
                f.write("\n\\end{minted}\n\n")
        
        # PART 3: Sillari
        f.write("% " + "="*70 + "\n")
        f.write("% PART 3: SILLARI'S KRIPKE SEMANTICS (Sillari_improved.lean)\n")
        f.write("% " + "="*70 + "\n\n")
        
        if sillari_data.get('frame_definition'):
            f.write("% Multi-Agent Kripke Frame\n")
            f.write("\\begin{minted}{lean}\n")
            f.write(sillari_data['frame_definition'])
            f.write("\n\\end{minted}\n\n")
        
        if sillari_data.get('kripke_definitions'):
            f.write("% Kripke Semantics Definitions\n")
            for name, code in sillari_data['kripke_definitions']:
                f.write(f"% {name}\n")
                f.write("\\begin{minted}{lean}\n")
                f.write(code)
                f.write("\n\\end{minted}\n\n")
        
        if sillari_data.get('crb_definition'):
            f.write("% Transitive Closure and CRB\n")
            f.write("\\begin{minted}{lean}\n")
            f.write(sillari_data['crb_definition'])
            f.write("\n\\end{minted}\n\n")
        
        # Axiom Proofs
        if sillari_data.get('axiom_proofs'):
            f.write("% " + "="*70 + "\n")
            f.write("% PROVABLE AXIOMS (B1, B2, B4, B5, B6, B10, B11)\n")
            f.write("% " + "="*70 + "\n\n")
            for name, code in sillari_data['axiom_proofs']:
                f.write(f"% Axiom {name}\n")
                f.write("\\begin{minted}{lean}\n")
                f.write(code)
                f.write("\n\\end{minted}\n\n")
        
        # Counterexamples - THE MAIN CONTRIBUTION
        if sillari_data.get('counterexamples'):
            f.write("% " + "="*70 + "\n")
            f.write("% COUNTEREXAMPLES: FAILURES OF SILLARI'S FORMALIZATION\n")
            f.write("% These are the main results showing Sillari's approach fails\n")
            f.write("% " + "="*70 + "\n\n")
            for name, code in sillari_data['counterexamples']:
                f.write(f"% {name}\n")
                f.write("\\begin{minted}{lean}\n")
                f.write(code)
                f.write("\n\\end{minted}\n\n")

def compute_statistics(project_dir):
    """Compute statistics about the formalization"""
    project_path = Path(project_dir)
    
    # Get .lean files from direct directory first
    lean_files = list(project_path.glob("*.lean"))
    # Also check subdirectories
    lean_files.extend([f for f in project_path.rglob("*.lean") if f not in lean_files])
    
    stats = {
        'files': len(lean_files),
        'total_lines': 0,
        'code_lines': 0,
        'definitions': 0,
        'axioms': 0,
        'theorems': 0,
        'lemmas': 0,
        'counterexamples': 0,
        'by_file': {}
    }
    
    for lean_file in lean_files:
        file_stats = {
            'total_lines': 0,
            'code_lines': 0,
            'definitions': 0,
            'axioms': 0,
            'theorems': 0,
            'lemmas': 0,
            'counterexamples': 0
        }
        
        with open(lean_file, 'r', encoding='utf-8') as f:
            content = f.read()
            lines = content.split('\n')
            
            file_stats['total_lines'] = len(lines)
            
            # Count non-comment, non-empty lines
            code_lines = []
            in_block_comment = False
            for line in lines:
                stripped = line.strip()
                if '/-' in stripped:
                    in_block_comment = True
                if '-/' in stripped:
                    in_block_comment = False
                    continue
                if not in_block_comment and stripped and not stripped.startswith('--'):
                    code_lines.append(line)
            
            file_stats['code_lines'] = len(code_lines)
            
            # Count constructs
            file_stats['definitions'] = len(re.findall(r'\bdef\s+\w+', content))
            file_stats['axioms'] = len(re.findall(r'\baxiom\s+\w+', content))
            file_stats['theorems'] = len(re.findall(r'\btheorem\s+\w+', content))
            file_stats['lemmas'] = len(re.findall(r'\blemma\s+\w+', content))
            
            # Count counterexamples
            file_stats['counterexamples'] = len(re.findall(r'lemma\s+\w*fails', content))
            file_stats['counterexamples'] += len(re.findall(r'lemma\s+lewis_s_2', content))
            
            # Add to totals
            stats['total_lines'] += file_stats['total_lines']
            stats['code_lines'] += file_stats['code_lines']
            stats['definitions'] += file_stats['definitions']
            stats['axioms'] += file_stats['axioms']
            stats['theorems'] += file_stats['theorems']
            stats['lemmas'] += file_stats['lemmas']
            stats['counterexamples'] += file_stats['counterexamples']
            
            stats['by_file'][lean_file.name] = file_stats
    
    return stats

def print_statistics(stats):
    """Print formatted statistics"""
    print("\n" + "="*70)
    print("LEWIS CONVENTION THEORY FORMALIZATION STATISTICS")
    print("="*70)
    print(f"Total Lean files:           {stats['files']}")
    print(f"Total lines:                {stats['total_lines']}")
    print(f"Code lines (no comments):   {stats['code_lines']}")
    print("-"*70)
    print(f"Definitions (def):          {stats['definitions']}")
    print(f"Axioms:                     {stats['axioms']}")
    print(f"Theorems:                   {stats['theorems']}")
    print(f"Lemmas:                     {stats['lemmas']}")
    print(f"Counterexamples:            {stats['counterexamples']}")
    print("="*70)
    print("\nPer-file breakdown:")
    print("-"*70)
    for filename, file_stats in stats['by_file'].items():
        print(f"\n{filename}:")
        print(f"  Lines: {file_stats['code_lines']} (code) / {file_stats['total_lines']} (total)")
        print(f"  Definitions: {file_stats['definitions']}, Axioms: {file_stats['axioms']}")
        print(f"  Theorems: {file_stats['theorems']}, Lemmas: {file_stats['lemmas']}")
        if file_stats['counterexamples'] > 0:
            print(f"  Counterexamples: {file_stats['counterexamples']}")
    print("="*70 + "\n")

def create_bibliography():
    """Create bibliography for Lewis convention theory"""
    bib = """@book{lewis1969convention,
  title={Convention: A Philosophical Study},
  author={Lewis, David K.},
  year={1969},
  publisher={Harvard University Press}
}

@article{sillari2005general,
  title={A General Framework for Modeling Common Knowledge Logic},
  author={Sillari, Giacomo},
  journal={Logic and the Foundations of Game and Decision Theory},
  pages={206--228},
  year={2005}
}

@article{sillari2008quantified,
  title={Quantified Logic of Awareness and Impossible Possible Worlds},
  author={Sillari, Giacomo},
  journal={Review of Symbolic Logic},
  volume={1},
  number={4},
  pages={514--529},
  year={2008}
}

@article{cubitt2003common,
  title={Common Knowledge, Salience and Convention: A Reconstruction of David Lewis' Game Theory},
  author={Cubitt, Robin P. and Sugden, Robert},
  journal={Economics and Philosophy},
  volume={19},
  number={2},
  pages={175--210},
  year={2003}
}

@article{artemov2008justification,
  title={The Logic of Justification},
  author={Artemov, Sergei N.},
  journal={The Review of Symbolic Logic},
  volume={1},
  number={4},
  pages={477--513},
  year={2008}
}

@inproceedings{moura2015lean,
  title={The Lean Theorem Prover},
  author={de Moura, Leonardo and Kong, Soonho and Avigad, Jeremy and van Doorn, Floris and von Raumer, Jakob},
  booktitle={International Conference on Automated Deduction},
  pages={378--388},
  year={2015}
}

@article{aumann1976agreeing,
  title={Agreeing to Disagree},
  author={Aumann, Robert J.},
  journal={The Annals of Statistics},
  volume={4},
  number={6},
  pages={1236--1239},
  year={1976}
}

@book{fagin1995reasoning,
  title={Reasoning About Knowledge},
  author={Fagin, Ronald and Halpern, Joseph Y. and Moses, Yoram and Vardi, Moshe Y.},
  year={1995},
  publisher={MIT Press}
}
"""
    return bib

if __name__ == "__main__":
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python extract_lewis.py <project_directory> [output_file]")
        print("Example: python extract_lewis.py ../lewis lewis_snippets.tex")
        sys.exit(1)
    
    project_dir = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else "lewis_snippets.tex"
    
    print(f"Processing Lewis Convention Theory project: {project_dir}")
    print(f"Output file: {output_file}\n")
    
    # Compute and display statistics
    stats = compute_statistics(project_dir)
    print_statistics(stats)
    
    # Generate LaTeX snippets
    print("Generating LaTeX snippets...")
    generate_latex_output(project_dir, output_file)
    print(f"✓ Generated: {output_file}\n")
    
    # Create bibliography
    bib_file = "lewis_references.bib"
    with open(bib_file, 'w') as f:
        f.write(create_bibliography())
    print(f"✓ Generated: {bib_file}\n")
    
    print("="*70)
    print("NEXT STEPS")
    print("="*70)
    print("1. Review the generated snippets in:", output_file)
    print("2. Edit paper.tex and include relevant snippets")
    print("3. Compile with: pdflatex -shell-escape paper.tex")
    print("4. Update the abstract with these numbers:")
    print(f"   - Total lines of code: {stats['code_lines']}")
    print(f"   - Total lemmas/theorems: {stats['lemmas'] + stats['theorems']}")
    print(f"   - Counterexamples: {stats['counterexamples']}")
    print("="*70)
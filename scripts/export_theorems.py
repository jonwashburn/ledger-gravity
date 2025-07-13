#!/usr/bin/env python3

import re
import os

# Extract theorems from Lean files
def export_theorems(input_dir='LedgerGravity', output_file='docs/theorems.tex'):
    theorems = []
    for file in os.listdir(input_dir):
        if file.endswith('.lean'):
            with open(os.path.join(input_dir, file), 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
                # Simple regex for theorems
                matches = re.findall(r'theorem (\w+) .*? := by\n(.*?)^$', content, re.DOTALL | re.MULTILINE)
                for name, body in matches:
                    theorems.append(rf'\subsection{{{name}}}\n\begin{{verbatim}}\n{body.strip()}\n\end{{verbatim}}')
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(rf'\section{{Exported Lean Theorems}}\n' + '\n\n'.join(theorems))

if __name__ == '__main__':
    export_theorems() 
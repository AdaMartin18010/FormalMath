#!/usr/bin/env python
# -*- coding: utf-8 -*-
import re
with open('concept_prerequisites.yaml', 'r', encoding='utf-8') as f:
    content = f.read()

# Find concept definition (starts with "  - concept_id:")
concept_id = "fourier_analysis"
pattern = f'  - concept_id: "{concept_id}"'
idx = content.find(pattern)
if idx >= 0:
    end = content.find('  - concept_id:', idx + 20)
    if end < 0:
        end = idx + 1000
    block = content[idx:end]
    print(block)
    print("\n" + "="*50)
    print("Has msc_primary:", 'msc_primary:' in block)
else:
    print(f"Concept {concept_id} not found!")

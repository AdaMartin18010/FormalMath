#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Add final 8 MSC codes"""

import yaml

with open('concept_prerequisites.yaml', 'r', encoding='utf-8') as f:
    content = f.read()

# MSC codes to add
msc_additions = {
    'fourier_analysis': ('42Bxx', ['42A38']),
    'lie_group': ('22E15', ['22Exx']),
    'algebraic_topology': ('55Nxx', ['55Mxx']),
    'markov_chain': ('60J10', ['60Jxx']),
    'martingale': ('60G42', ['60Gxx']),
    'kalman_filter': ('93E11', ['60G35']),
    'shannon_entropy': ('94A17', ['94Axx']),
    'rsa': ('94A60', ['11Axx']),
}

updated = 0
for concept_id, (primary, secondary) in msc_additions.items():
    pattern = f'concept_id: "{concept_id}"'
    if pattern in content:
        idx = content.find(pattern)
        next_concept = content.find('concept_id:', idx + len(pattern))
        block = content[idx:next_concept if next_concept > 0 else idx + 1000]
        
        if 'msc_primary:' in block:
            print(f'Skipping {concept_id} - already has MSC')
            continue
        
        sec_str = ', '.join([f'"{s}"' for s in secondary])
        msc_block = f'\n    msc_primary: "{primary}"\n    msc_secondary: [{sec_str}]'
        
        diff_idx = content.find('difficulty:', idx)
        if diff_idx > 0:
            # Find line start
            line_start = content.rfind('\n', 0, diff_idx)
            content = content[:line_start] + msc_block + content[line_start:]
            updated += 1
            print(f'Updated {concept_id}')

with open('concept_prerequisites.yaml', 'w', encoding='utf-8') as f:
    f.write(content)

print(f'\nTotal updated: {updated}')

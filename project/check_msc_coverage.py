#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Check MSC coverage in concept_prerequisites.yaml"""

import yaml
import re

def check_coverage():
    with open('concept_prerequisites.yaml', 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Count concept blocks with concept_id
    concept_blocks = re.findall(r'- concept_id: "([^"]+)"', content)
    total = len(concept_blocks)
    print(f'Total concepts: {total}')
    
    # Count with msc_primary
    msc_blocks = re.findall(r'msc_primary:', content)
    with_msc = len(msc_blocks)
    print(f'With MSC primary: {with_msc}')
    
    # Coverage percentage
    if total > 0:
        print(f'Current coverage: {with_msc/total*100:.1f}%')
    
    # Target: 60%
    target = int(total * 0.6)
    print(f'Target (60%): {target}')
    print(f'Need to add: {target - with_msc}')
    
    # Find concepts without MSC
    lines = content.split('\n')
    current_concept = None
    concepts_without_msc = []
    has_msc = False
    
    for line in lines:
        concept_match = re.search(r'- concept_id: "([^"]+)"', line)
        if concept_match:
            if current_concept and not has_msc:
                concepts_without_msc.append(current_concept)
            current_concept = concept_match.group(1)
            has_msc = False
        elif 'msc_primary:' in line:
            has_msc = True
    
    # Don't forget the last concept
    if current_concept and not has_msc:
        concepts_without_msc.append(current_concept)
    
    print(f'\nConcepts without MSC ({len(concepts_without_msc)}):')
    for c in concepts_without_msc[:50]:
        print(f'  - {c}')
    
    if len(concepts_without_msc) > 50:
        print(f'  ... and {len(concepts_without_msc) - 50} more')

if __name__ == '__main__':
    check_coverage()

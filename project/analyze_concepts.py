#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Analyze concepts in concept_prerequisites.yaml"""

import yaml
import re
from collections import defaultdict

def analyze():
    with open('concept_prerequisites.yaml', 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Try to parse as YAML
    try:
        data = yaml.safe_load(content)
        concepts = data.get('concepts', [])
        
        total = len(concepts)
        with_msc = sum(1 for c in concepts if c.get('msc_primary'))
        
        print(f'Total concept definitions: {total}')
        print(f'With MSC primary: {with_msc}')
        print(f'Current coverage: {with_msc/total*100:.1f}%')
        
        # Target: 60%
        target = int(total * 0.6)
        print(f'Target (60%): {target}')
        print(f'Need to add: {target - with_msc}')
        
        # Group by category
        by_category = defaultdict(list)
        for c in concepts:
            cat = c.get('category', 'Unknown')
            by_category[cat].append(c)
        
        print(f'\nConcepts by category:')
        for cat, items in sorted(by_category.items()):
            with_msc_cat = sum(1 for c in items if c.get('msc_primary'))
            print(f'  {cat}: {len(items)} total, {with_msc_cat} with MSC ({with_msc_cat/len(items)*100:.0f}%)')
        
        # List concepts without MSC by category
        print(f'\nConcepts without MSC by category:')
        for cat, items in sorted(by_category.items()):
            without_msc = [c for c in items if not c.get('msc_primary')]
            if without_msc:
                print(f'\n  {cat} ({len(without_msc)} missing):')
                for c in without_msc[:10]:
                    print(f'    - {c.get("concept_id")}: {c.get("name")}')
                if len(without_msc) > 10:
                    print(f'    ... and {len(without_msc) - 10} more')
        
        return concepts
        
    except Exception as e:
        print(f'Error parsing YAML: {e}')
        return []

if __name__ == '__main__':
    analyze()

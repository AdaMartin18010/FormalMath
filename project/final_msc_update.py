#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Final MSC update to reach 60% coverage"""

import re

# Select 10 most important concepts from remaining
FINAL_MSC = {
    # 分析学 (5个)
    "fourier_analysis": {"primary": "42Bxx", "secondary": ["42A38", "42Cxx"]},
    "harmonic_analysis": {"primary": "43Axx", "secondary": ["42Bxx", "22E30"]},
    "sobolev_spaces": {"primary": "46E35", "secondary": ["46Fxx", "35Sxx"]},
    "partial_differential_equations": {"primary": "35Jxx", "secondary": ["35Kxx", "35Lxx"]},
    "asymptotic_analysis": {"primary": "41A60", "secondary": ["30E15", "34E05"]},
    
    # 代数学 (3个)
    "matrix": {"primary": "15Axx", "secondary": ["15A09", "65Fxx"]},
    "lie_algebra": {"primary": "17Bxx", "secondary": ["22E60", "17Bxx"]},
    "category_theory": {"primary": "18Axx", "secondary": ["18Bxx", "18Cxx"]},
    
    # 几何拓扑 (2个)
    "algebraic_topology": {"primary": "55Nxx", "secondary": ["55Mxx", "55Pxx"]},
    "index_theorem": {"primary": "58J20", "secondary": ["19K56", "58Jxx"]},
}

def update_final():
    with open('concept_prerequisites.yaml', 'r', encoding='utf-8') as f:
        content = f.read()
    
    updated_count = 0
    
    for concept_id, msc_data in FINAL_MSC.items():
        primary = msc_data['primary']
        secondary = msc_data.get('secondary', [])
        
        msc_lines = f'    msc_primary: "{primary}"'
        if secondary:
            sec_str = ', '.join([f'"{s}"' for s in secondary])
            msc_lines += f'\n    msc_secondary: [{sec_str}]'
        
        pattern = rf'(- concept_id: "{concept_id}".*?category: "([^"]+)".*?)(\n    difficulty:)'
        
        match = re.search(pattern, content, re.DOTALL)
        if match:
            block = match.group(1)
            suffix = match.group(3)
            
            if 'msc_primary:' in block:
                print(f"Skipping {concept_id} - already has MSC")
                continue
            
            new_block = block + '\n' + msc_lines + suffix
            content = content.replace(block + suffix, new_block)
            updated_count += 1
            print(f"Updated: {concept_id}")
    
    with open('concept_prerequisites.yaml', 'w', encoding='utf-8') as f:
        f.write(content)
    
    print(f"\nFinal update: {updated_count} concepts updated")
    return updated_count

if __name__ == '__main__':
    update_final()

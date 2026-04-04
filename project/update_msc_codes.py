#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Update MSC codes in concept_prerequisites.yaml"""

import yaml
import re
from msc_encoding_plan import MSC_ENCODING

# Additional MSC codes for existing categories
ADDITIONAL_MSC = {
    # 分析学缺失 (12个)
    "fourier_analysis": {"primary": "42Bxx", "secondary": ["42A38", "42Cxx"]},
    "complex_analysis": {"primary": "30Cxx", "secondary": ["30Dxx", "30Exx"]},
    "harmonic_analysis": {"primary": "43Axx", "secondary": ["42Bxx", "22E30"]},
    "measure_theory": {"primary": "28Axx", "secondary": ["28Cxx", "60A10"]},
    "lebesgue_integral": {"primary": "28A25", "secondary": ["26A42", "46E30"]},
    "functional_analysis": {"primary": "46Axx", "secondary": ["46Bxx", "46Cxx"]},
    "operator_theory": {"primary": "47Axx", "secondary": ["47Bxx", "47Cxx"]},
    "sobolev_spaces": {"primary": "46E35", "secondary": ["46Fxx", "35Sxx"]},
    "variational_methods": {"primary": "49Jxx", "secondary": ["49Kxx", "58E05"]},
    "differential_equations": {"primary": "34Axx", "secondary": ["34Bxx", "34Cxx"]},
    "partial_differential_equations": {"primary": "35Jxx", "secondary": ["35Kxx", "35Lxx"]},
    "asymptotic_analysis": {"primary": "41A60", "secondary": ["30E15", "34E05"]},
    
    # 代数学缺失 (15个)
    "linear_algebra": {"primary": "15Axx", "secondary": ["15A03", "15A06"]},
    "vector_space": {"primary": "15A03", "secondary": ["46Axx", "15Axx"]},
    "matrix": {"primary": "15Axx", "secondary": ["15A09", "65Fxx"]},
    "eigenvalue": {"primary": "15A18", "secondary": ["15Axx", "65F15"]},
    "jordan_normal_form": {"primary": "15A21", "secondary": ["15Axx"]},
    "homological_algebra": {"primary": "18Gxx", "secondary": ["13Dxx", "16Exx"]},
    "group_representation": {"primary": "20Cxx", "secondary": ["20G05", "22Exx"]},
    "character_theory": {"primary": "20C15", "secondary": ["20Cxx"]},
    "solvable_group": {"primary": "20F16", "secondary": ["20D10", "20Exx"]},
    "lie_group": {"primary": "22E15", "secondary": ["22Exx", "20Gxx"]},
    "ring_theory": {"primary": "16Y60", "secondary": ["16Exx"]},
    "module_theory": {"primary": "16Dxx", "secondary": ["13Cxx", "18Fxx"]},
    "field_extension": {"primary": "12Fxx", "secondary": ["12E05", "11R32"]},
    "galois_theory": {"primary": "12F10", "secondary": ["11R32", "12Fxx"]},
    "tensor_algebra": {"primary": "15A69", "secondary": ["11E39", "15Axx"]},
    
    # 几何拓扑缺失 (8个)
    "differential_form": {"primary": "58A10", "secondary": ["53C65", "58Axx"]},
    "stokes_theorem": {"primary": "58C35", "secondary": ["58A10", "58Axx"]},
    "characteristic_class": {"primary": "57R20", "secondary": ["55R40", "57Rxx"]},
    "morse_theory": {"primary": "58E05", "secondary": ["57R70", "58Exx"]},
    "index_theorem": {"primary": "58J20", "secondary": ["19K56", "58Jxx"]},
    "symplectic_geometry": {"primary": "53D05", "secondary": ["37Jxx", "53Dxx"]},
    "complex_geometry": {"primary": "32Qxx", "secondary": ["32Cxx", "53C55"]},
    "algebraic_topology": {"primary": "55Nxx", "secondary": ["55Mxx", "55Pxx"]},
}

# Merge all MSC codes
ALL_MSC = {**MSC_ENCODING, **ADDITIONAL_MSC}

def update_msc_codes():
    # Read the original file
    with open('concept_prerequisites.yaml', 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Track updates
    updated_count = 0
    skipped_count = 0
    not_found = []
    
    # Process each concept
    for concept_id, msc_data in ALL_MSC.items():
        # Create the MSC primary line
        primary = msc_data['primary']
        secondary = msc_data.get('secondary', [])
        
        # Build replacement
        msc_lines = f'    msc_primary: "{primary}"'
        if secondary:
            sec_str = ', '.join([f'"{s}"' for s in secondary])
            msc_lines += f'\n    msc_secondary: [{sec_str}]'
        
        # Pattern to find the concept and check if it has msc_primary
        # Look for concept block
        pattern = rf'(- concept_id: "{concept_id}".*?category: "([^"]+)".*?)(\n    difficulty:)'
        
        match = re.search(pattern, content, re.DOTALL)
        if match:
            block = match.group(1)
            category = match.group(2)
            suffix = match.group(3)
            
            # Check if already has msc_primary
            if 'msc_primary:' in block:
                skipped_count += 1
                continue
            
            # Add MSC codes before difficulty
            new_block = block + '\n' + msc_lines + suffix
            content = content.replace(block + suffix, new_block)
            updated_count += 1
        else:
            not_found.append(concept_id)
    
    # Write updated file
    with open('concept_prerequisites.yaml', 'w', encoding='utf-8') as f:
        f.write(content)
    
    print(f"MSC Encoding Update Report")
    print(f"=" * 50)
    print(f"Total MSC codes prepared: {len(ALL_MSC)}")
    print(f"Updated: {updated_count}")
    print(f"Skipped (already has MSC): {skipped_count}")
    print(f"Not found in file: {len(not_found)}")
    if not_found:
        print(f"\nNot found concepts:")
        for c in not_found:
            print(f"  - {c}")
    
    return updated_count

if __name__ == '__main__':
    count = update_msc_codes()
    print(f"\nUpdated {count} concepts with MSC codes.")

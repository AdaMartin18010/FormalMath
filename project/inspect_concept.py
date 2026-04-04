#!/usr/bin/env python
# -*- coding: utf-8 -*-
import re
with open('concept_prerequisites.yaml', 'r', encoding='utf-8') as f:
    content = f.read()

# Find fourier_analysis
idx = content.find('concept_id: "fourier_analysis"')
if idx >= 0:
    end = content.find('concept_id:', idx + 30)
    print(content[idx:end])
    print("\n" + "="*50)
    print("Has msc_primary:", 'msc_primary:' in content[idx:end])

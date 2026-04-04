#!/usr/bin/env python
# -*- coding: utf-8 -*-
with open('concept_prerequisites.yaml', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Check first 100 lines
for i, line in enumerate(lines[:100], 1):
    if 'concept_id' in line:
        print(f"{i}: {line.rstrip()}")
    if i > 50 and 'concept_id' in line:
        break

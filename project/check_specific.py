#!/usr/bin/env python
# -*- coding: utf-8 -*-
import yaml
with open('concept_prerequisites.yaml', 'r', encoding='utf-8') as f:
    data = yaml.safe_load(f)

# Check specific concepts
to_check = ['lie_group', 'algebraic_topology', 'fourier_analysis', 'markov_chain', 'kalman_filter', 'rsa', 'lie_algebra', 'category_theory']
for c in data.get('concepts', []):
    if c.get('concept_id') in to_check:
        print(f"{c['concept_id']}: {c.get('msc_primary', 'NO MSC')}")

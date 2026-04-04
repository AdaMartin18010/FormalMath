#!/usr/bin/env python
# -*- coding: utf-8 -*-
import yaml

with open('concept_prerequisites.yaml', 'r', encoding='utf-8') as f:
    data = yaml.safe_load(f)

concept_id = "fourier_analysis"
for c in data.get('concepts', []):
    if c.get('concept_id') == concept_id:
        import json
        print(json.dumps(c, ensure_ascii=False, indent=2))
        break

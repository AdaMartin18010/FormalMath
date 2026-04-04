import yaml

with open('g:\\_src\\FormalMath\\project\\concept_prerequisites.yaml', 'r', encoding='utf-8') as f:
    data = yaml.safe_load(f)

concepts = data.get('concepts', [])
print(f"Total concepts: {len(concepts)}")
print()

for c in concepts:
    cat = c.get('category', 'Unknown')
    print(f"\"{c['concept_id']}\": \"{c['name']} ({cat})\",")
